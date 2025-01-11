/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Matej Bölcskei <mboelcskei@ethz.ch>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/consteval.h"
#include "kernel/celltypes.h"
#include <string.h>
#include "selection.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static SigMap assign_map;
SigSet<RTLIL::Cell*, RTLIL::sort_by_name_id<RTLIL::Cell>> sig2driver;

// ID($lt), ID($le), ID($eq), ID($ne), ID($eqx), ID($nex), ID($ge), ID($gt)
// ID($add), ID($sub), ID($mul), ID($div), ID($mod), ID($divfloor), ID($modfloor), ID($pow)
// ID($shift), ID($shiftx)
// ID($shl), ID($shr), ID($sshl), ID($sshr)
// ID($reduce_and), ID($reduce_or), ID($reduce_xor), ID($reduce_xnor), ID($reduce_bool)
// ID($and), ID($or), ID($xor), ID($xnor)
// ID($not), ID($pos), ID($neg)

struct InjectExpandPass : public Pass {
	InjectExpandPass() : Pass("inject_expand", "expand AMT tables") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    inject_expand [selection]\n");
		log("\n");
		log("This pass expands AMT tables.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INJECT_EXPAND pass (expanding AMT tables).\n");
		extra_args(args, 1, design);

        CellTypes ct(design);

		for (auto module : design->selected_modules()) {
			assign_map.set(module);

			sig2driver.clear();
			for (auto cell : module->cells()) {
				// TODO extend this list
				if (cell->type.in(ID($eq), ID($and), ID($or), ID($not))) {
					for (auto &connection : cell->connections()) {
						RTLIL::SigSpec signal = assign_map(connection.second);
						RTLIL::SigSpec filtered_signal;
						for (auto bit : signal.bits()) {
							// TODO discuss the "_T" business with Flavien
							// if (bit.is_wire() && (bit.wire->name.str().at(0) != '\\' || bit.wire->name.str().find("_T") != std::string::npos || bit.wire->name.str().find("_1") != std::string::npos || bit.wire->name.str().find("_2") != std::string::npos || bit.wire->name.str().find("_3") != std::string::npos || bit.wire->name.str().find("_4") != std::string::npos || bit.wire->name.str().find("_5") != std::string::npos || bit.wire->name.str().find("_6") != std::string::npos || bit.wire->name.str().find("_7") != std::string::npos || bit.wire->name.str().find("_8") != std::string::npos || bit.wire->name.str().find("_9") != std::string::npos)) {
							if (bit.is_wire() && (bit.wire->name.str().at(0) != '\\')) {
								filtered_signal.append(bit);
							}
							// filtered_signal.append(bit);
						}
						if (ct.cell_output(cell->type, connection.first)) {
							sig2driver.insert(filtered_signal, cell);
						}
					}
				}
			}

			std::vector<RTLIL::Cell*> amt_cells;
			for (auto cell : module->selected_cells())
				if (cell->type == ID($amt))
					amt_cells.push_back(cell);
			for (auto amt_cell : amt_cells) {
				// if (amt_cell->name != "$amt$$flatten\\csr.$0\\reg_mstatus_gva[0:0]$33283") continue;
				log("Expanding AMT %s from module %s.\n", amt_cell->name.c_str(), module->name.c_str());

				RTLIL::SigSpec select = amt_cell->getPort(ID::S);
				RTLIL::SigSpec original_select = amt_cell->getPort(ID::S);

				std::vector<selection_t> selections;
				copy_from_cell(amt_cell, selections);

				std::vector<selection_t> original_selections;
				copy_from_cell(amt_cell, original_selections);

				int position = 0;
				for (std::set<RTLIL::Cell *> worklist = sig2driver.find(assign_map(select)); !worklist.empty(); worklist = sig2driver.find(assign_map(select.extract(position, select.size() - position)))) {
					position = select.size();
					for (auto cell : worklist) {
						RTLIL::SigSpec cell_input, cell_output, full_output;
						for (auto &p : cell->connections())
							if (ct.cell_input(cell->type, p.first))
								cell_input.append(assign_map(p.second));
							else
								cell_output.append(assign_map(p.second));
						cell_input.sort_and_unify();
						if (cell->type.in(ID($and), ID($or))) {
							RTLIL::SigSpec left, right;
							for (int i = 0; i < cell_output.size(); ++i) {
								if (!select.extract(cell_output.extract(i)).empty()) {
									left.append(cell_input.extract(cell_output.size()+i));
									right.append(cell_input.extract(i));
								}
							}
							left.append(right);
							cell_input = left;
						} else if (cell->type == ID($not)) {
							RTLIL::SigSpec filtered_input;
							for (int i = 0; i < cell_output.size(); ++i) {
								if (!select.extract(cell_output.extract(i)).empty()) {
									filtered_input.append(cell_input.extract(i));
								}
							}
							cell_input = filtered_input;
						}
						cell_input.remove_const();
						if (cell_input.size() > 8) continue;

						// TODO might have to assign map
						full_output = cell_output;
						cell_output = cell_output.extract(select);

						log("Merging cell: %s\n", cell->name.c_str());
						log("Type: %s\n", cell->type.c_str());
						log("Output: %s\n", log_signal(cell_output));
						log("Input: %s\n", log_signal(cell_input));
						log_flush();

						std::vector<std::pair<RTLIL::Const, RTLIL::Const>> truth_tab;
						for (unsigned long long i = 0; i < (1ULL << cell_input.size()); i++) {
							RTLIL::Const in_val(i, cell_input.size());
							RTLIL::SigSpec A, B, S;
							if (cell->hasPort(ID::A))
								A = assign_map(cell->getPort(ID::A));
							if (cell->hasPort(ID::B))
								B = assign_map(cell->getPort(ID::B));
							if (cell->hasPort(ID::S))
								S = assign_map(cell->getPort(ID::S));
							A.replace(cell_input, RTLIL::SigSpec(in_val));
							if (cell->hasPort(ID::A))
								A.replace(assign_map(cell->getPort(ID::A)), RTLIL::SigSpec(RTLIL::Const(State::S0, A.size())));
							B.replace(cell_input, RTLIL::SigSpec(in_val));
							if (cell->hasPort(ID::B))
								B.replace(assign_map(cell->getPort(ID::B)), RTLIL::SigSpec(RTLIL::Const(State::S0, B.size())));
							S.replace(cell_input, RTLIL::SigSpec(in_val));
							if (cell->hasPort(ID::S))
								S.replace(assign_map(cell->getPort(ID::S)), RTLIL::SigSpec(RTLIL::Const(State::S0, S.size())));
							log_assert(A.is_fully_const());
							log_assert(B.is_fully_const());
							log_assert(S.is_fully_const());
							RTLIL::SigSpec out_val = cell_output;
							out_val.replace(full_output, ct.eval(cell, A.as_const(), B.as_const(), S.as_const()));
							truth_tab.push_back({out_val.as_const(), in_val});
						}

						bool merged = true;
						while (merged) {
							merged = false;
							for (size_t i = 0; i < truth_tab.size(); ++i) {
								for (size_t j = i + 1; j < truth_tab.size(); ++j) {
									if (truth_tab.at(i).first != truth_tab.at(j).first) continue;
									int matching = 0;
									int index;
									for (int k = 0; k < cell_input.size(); ++k) {
										if (truth_tab.at(i).second.bits.at(k) == truth_tab.at(j).second.bits.at(k)) {
											++matching;
										} else {
											index = k;
										}
									}
									if (matching != cell_input.size() - 1) continue;

									truth_tab.at(i).second.bits.at(index) = State::Sa;
									truth_tab.erase(truth_tab.begin() + j);
									--j;
									merged = true;
									break;
								}
							}
						}

						for (size_t i = 0; i < truth_tab.size(); ++i) {
							log("%s %s\n", log_signal(truth_tab.at(i).first), log_signal(truth_tab.at(i).second));
						}

						RTLIL::SigSpec old_select = select;
						for (auto select_bit : cell_input) {
							if (select.extract(select_bit).empty()) {
								select.append(select_bit);
							}
						}
						// select.remove(cell_output);

						for (size_t i = 0; i < selections.size(); ++i) {
							RTLIL::SigSpec selection_sig = cell_output;
							RTLIL::Const selection_output;
							RTLIL::Const selection_input;
							cell_output.replace(old_select, selections.at(i).select, &selection_sig);
							selection_output = selection_sig.as_const();
							RTLIL::SigSpec filtered_selection_sig;
							selection_sig = cell_input;
							cell_input.replace(old_select, selections.at(i).select, &selection_sig);
							for (auto bit : selection_sig.bits()) {
								if (bit.is_wire()) {
									filtered_selection_sig.append(State::Sa);
								} else {
									filtered_selection_sig.append(bit.data);
								}
							}
							selection_input = filtered_selection_sig.as_const();

							size_t num_selections = 0;
							RTLIL::SigSpec new_select = select;
							new_select.replace(old_select, selections.at(i).select);
							if (selection_output == RTLIL::Const(State::Sa, selection_output.size())) {
								new_select.replace(cell_input, RTLIL::Const(State::Sa, cell_input.size()));
								selections.insert(selections.begin()+i+num_selections+1, {new_select.as_const(), selections.at(i).output, selections.at(i).buggy});
								++num_selections;
							} else {
								for (size_t j = 0; j < truth_tab.size(); ++j) {
									bool matching = true;
									for (int k = 0; k < cell_output.size(); ++k) {
										if (truth_tab.at(j).first.bits.at(k) != State::Sa && selection_output.bits.at(k) != State::Sa && truth_tab.at(j).first.bits.at(k) != selection_output.bits.at(k)) {
											matching = false;
											break;
										}
									}
									if (!matching) continue;

									matching = true;
									for (int k = 0; k < cell_input.size(); ++k) {
										if (truth_tab.at(j).second.bits.at(k) == State::Sa) {
											select.replace(cell_input.bits().at(k), selection_input.bits.at(k), &new_select);
										} else if (selection_input.bits.at(k) == State::Sa) {
											select.replace(cell_input.bits().at(k), truth_tab.at(j).second.bits.at(k), &new_select);
										} else if (truth_tab.at(j).second.bits.at(k) == selection_input.bits.at(k)) {
											select.replace(cell_input.bits().at(k), selection_input.bits.at(k), &new_select);
										} else {
											matching = false;
										}
									}
									if (!matching) continue;
									
									selections.insert(selections.begin()+i+num_selections+1, {new_select.as_const(), selections.at(i).output, selections.at(i).buggy});
									++num_selections;
								}
							}
							selections.erase(selections.begin() + i);

							i += num_selections - 1;
						}

						amt_cell->unsetPort(ID::S);
						amt_cell->setPort(ID::S, select);
						log("Generated new selections.\n");
						log_amt(amt_cell, selections);
						if (selections.size() > 100) break;
					}
					if (selections.size() > 100) {
						log("Breaking.\n");
						break;
					}
				}
				
				std::vector<selection_t> filtered_selections;
				for (auto selection : original_selections) {
					for (auto expanded_selection : selections) {
						RTLIL::SigSpec zoinks = original_select;
						zoinks.replace(select, expanded_selection.select);
						if (zoinks == selection.select) {
							filtered_selections.push_back(selection);
							break;
						}
					}
				}
				amt_cell->unsetPort(ID::S);
				amt_cell->setPort(ID::S, original_select);
				copy_to_cell(amt_cell, filtered_selections);
				log("Filtered AMT:\n");
				log_amt(amt_cell, filtered_selections);
			}
		}

        assign_map.clear();
		sig2driver.clear();
	}
} InjectExpandPass;

PRIVATE_NAMESPACE_END
