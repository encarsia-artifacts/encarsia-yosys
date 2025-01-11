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
#include "selection.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static RTLIL::Module *module;
static SigMap assign_map;
typedef std::pair<RTLIL::IdString, RTLIL::IdString> sig2driver_entry_t;
static SigSet<sig2driver_entry_t> sig2driver;

struct sig2val_t {RTLIL::SigSpec input_sig; RTLIL::Const input_val;};
struct selection_raw_t {std::vector<sig2val_t> select; RTLIL::SigSpec output;};

static bool abstract_tree(RTLIL::SigSpec sig, RTLIL::SigSpec &input, RTLIL::SigSpec &select, const RTLIL::SigSpec &output, std::vector<sig2val_t> &current_selection, std::vector<selection_raw_t> &selections)
{
	sig.extend_u0(output.size(), false);
	assign_map.apply(sig);
	if (sig.is_fully_const()) {
		if (sig.is_fully_def()) {
			log("  input signal %s found in mux tree.\n", log_signal(sig));
			input.append(sig);
			selections.push_back({current_selection, sig});
		}
		return true;
	}
	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(sig, cellport_list);

	if (GetSize(cellport_list) > 1) {
		log("  found %d combined drivers for input signal %s.\n", GetSize(cellport_list), log_signal(sig));
		return false;
	}

	if (GetSize(cellport_list) < 1) {
		log("  found no driver for input signal %s.\n", log_signal(sig));
		return false;
	}

	if (selections.size() > 48) {
		log("  the AMT is too large to abstract.\n");
		return false;
	}

	for (auto &cellport : cellport_list)
	{
		RTLIL::Cell *cell = module->cells_.at(cellport.first);
		if ((cell->type != ID($mux) && cell->type != ID($pmux)) || cellport.second != ID::Y) {
			// TODO possibly check whether sig is an existing input
			log("  input signal %s found in mux tree.\n", log_signal(sig));
			input.append(sig);
			selections.push_back({current_selection, sig});
			return true;
		}

		RTLIL::SigSpec sig_a = assign_map(cell->getPort(ID::A));
		RTLIL::SigSpec sig_b = assign_map(cell->getPort(ID::B));
		RTLIL::SigSpec sig_s = assign_map(cell->getPort(ID::S));
		RTLIL::SigSpec sig_y = assign_map(cell->getPort(ID::Y));

		RTLIL::SigSpec sig_aa = sig;
		sig_aa.replace(sig_y, sig_a);

		RTLIL::SigSpec sig_bb;
		for (int i = 0; i < GetSize(sig_b)/GetSize(sig_a); i++) {
			RTLIL::SigSpec s = sig;
			s.replace(sig_y, sig_b.extract(i*GetSize(sig_a), GetSize(sig_a)));
			sig_bb.append(s);
		}

		for (auto sig_s_bit : sig_s) {
			if (select.extract(sig_s_bit).empty()) {
				log("  found select signal: %s\n", log_signal(sig_s_bit));
				select.append(sig_s_bit);
			}
		}

		// TODO check if select signal not already in current_selection if so error

		current_selection.push_back({sig_s, RTLIL::Const(0, sig_s.size())});
		if (!abstract_tree(sig_aa, input, select, output, current_selection, selections))
			return false;

		for (int i = 0; i < GetSize(sig_bb)/GetSize(sig_aa); i++) {
			current_selection.pop_back();
			// TODO maybe wrong shift direction
			current_selection.push_back({sig_s, RTLIL::Const(1<<i, sig_s.size())});
			if (!abstract_tree(sig_bb.extract(i*GetSize(sig_aa), GetSize(sig_aa)), input, select, output, current_selection, selections))
				return false;
		}
		current_selection.pop_back();
	}

	return true;
}

static void extract_tree(RTLIL::Wire *wire)
{
	log("Extracting mux tree %s from module %s.\n", wire->name.c_str(), module->name.c_str());

	RTLIL::SigSpec select, input, output = assign_map(RTLIL::SigSpec(wire));
	std::vector<sig2val_t> current_selection;
	std::vector<selection_raw_t> selections_raw;
	if(!abstract_tree(output, input, select, output, current_selection, selections_raw)){
		log("  mux tree abstraction failed!\n");
		return;
	}
	
	if (selections_raw.size() < 4) {
		log("  the AMT is too small to abstract.\n");
		return;
	}

	select.sort_and_unify();
	log("  select signal: %s\n", log_signal(select));

	// unifies the select signal order across the selects
	std::vector<selection_t> selections;
	for (auto &raw_selection : selections_raw){
		RTLIL::SigSpec pattern, with, other(select);
		for(auto sig2val : raw_selection.select){
			pattern.append(sig2val.input_sig);
			with.append(sig2val.input_val);
		}

		for(auto select_bit : select){
			if (pattern.extract(select_bit).empty()) {
				pattern.append(select_bit);
				with.append(RTLIL::SigBit(RTLIL::State::Sa));
			}
		}

		select.replace(pattern, with, &other);
		selections.push_back({other.as_const(), raw_selection.output, false});
	}

	// create amt cell

	RTLIL::Cell *amt_cell = module->addCell(stringf("$amt$%s$%d", wire->name.c_str(), autoidx++), ID($amt));
	amt_cell->setPort(ID::A, input);
	amt_cell->setPort(ID::S, select);
	amt_cell->setPort(ID::Y, output);
	amt_cell->attributes = wire->attributes;

	copy_to_cell(amt_cell, selections);

	// unconnect control outputs from old drivers

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(output, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = module->cells_.at(cellport.first);
		RTLIL::SigSpec port_sig = assign_map(cell->getPort(cellport.second));
		RTLIL::SigSpec unconn_sig = port_sig.extract(output);
		RTLIL::Wire *unconn_wire = module->addWire(stringf("$amt_unconnect$%d", autoidx++), unconn_sig.size());
		port_sig.replace(unconn_sig, RTLIL::SigSpec(unconn_wire), &cell->connections_[cellport.second]);
	}

	log_amt(amt_cell, selections);
}

struct InjectExtractPass : public Pass {
	InjectExtractPass() : Pass("inject_extract", "extract AMTs in the design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    inject_extract [selection]\n");
		log("\n");
		log("This pass extracts AMT cells in the design.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INJECT_EXTRACT pass (extracting AMTs from design).\n");
		extra_args(args, 1, design);

		CellTypes ct(design);

		for (auto mod : design->selected_modules())
		{
			if (mod->name.str().find("id_stage") != std::string::npos) continue;
			if (mod->name.str().find("maptable") != std::string::npos) continue;
			// TODO fix this monstrosity
			module = mod;
			assign_map.set(module);

			sig2driver.clear();
			for (auto cell : module->cells()) {
				for (auto &conn_it : cell->connections()) {
					if (ct.cell_output(cell->type, conn_it.first) || !ct.cell_known(cell->type)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2driver.insert(sig, sig2driver_entry_t(cell->name, conn_it.first));
					}
				}
			}

			std::vector<RTLIL::Wire*> wire_list;
			// TODO replace fsm_encoding
			for (auto wire : module->selected_wires()) {
				if (wire->attributes.count(ID::fsm_encoding) > 0 && wire->attributes[ID::fsm_encoding].decode_string() != "none"){
					std::string wire_name = wire->name.str();
					wire_list.push_back(wire);
				}
			}
			for (auto wire : wire_list)
				extract_tree(wire);
				// if (rand() % (wire_list.size()/500 + 1) == 0)
				// 	extract_tree(wire);
		}

		assign_map.clear();
		sig2driver.clear();
	}
} InjectExtractPass;

PRIVATE_NAMESPACE_END
