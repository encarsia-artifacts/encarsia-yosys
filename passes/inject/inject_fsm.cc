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

#include "kernel/register.h"
#include "kernel/log.h"
#include "../fsm/fsmdata.h"

#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <errno.h>
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void corrupt_transition(FsmData &fsm_data, FsmData::transition_t &transition)
{
	int source_state;

	do
	{
		source_state = std::rand() % fsm_data.state_table.size();
	}
	while (source_state == transition.state_out);

	transition.state_out = source_state;
}

static bool is_challenging(FsmData::transition_t &transition)
{
	// TODO replace placeholder
	return transition.ctrl_in.is_fully_def();
}

static RTLIL::Design *create_miter(RTLIL::Module *module, RTLIL::Cell *cell, FsmData &fsm_data, FsmData::transition_t &transition, std::vector<std::string> &observables)
{
	RTLIL::Design *miter_design = new RTLIL::Design;

	RTLIL::Module *miter_module = new RTLIL::Module;
	miter_module->name = "\\miter_" + module->name.str().substr(1);
	miter_design->add(miter_module);

	// Setup gold module
	RTLIL::Module *gold_module = module->clone();
	gold_module->name = "\\gold_" + module->name.str().substr(1);
	miter_design->add(gold_module);

	RTLIL::SigSpec gold_input = gold_module->cells_.at(cell->name)->getPort(ID::CTRL_IN);

	Pass::call(miter_design, "fsm_map");

	RTLIL::Wire *gold_state;
	RTLIL::SigSpec gold_observables;
	SigMap gold_sigmap(gold_module);

	for (auto observable : observables) {
		// TODO maybe "\\" + is not enough
		RTLIL::Wire *observable_wire = gold_module->wire("\\" + observable);
		if (!observable_wire) log_cmd_error("Observable %s is missing!\n", observable.c_str());
		gold_observables.append(observable_wire);
	}
	RTLIL::Wire *gold_observables_wire = gold_module->addWire("\\injection_observables", gold_observables.size());
	gold_observables_wire->port_output = true;
	gold_module->fixup_ports();
	gold_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gold_observables_wire), gold_sigmap(gold_observables)));

	// RTLIL::Wire *gold_input_wire = gold_module->addWire("\\injection_input", gold_input.size());
	// gold_input_wire->port_output = true;
	// gold_module->fixup_ports();
	// gold_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gold_input_wire), gold_sigmap(gold_input)));

	// gold_state = gold_module->wire(cell->parameters[ID::NAME].decode_string());
	// if (!gold_state) log_cmd_error("State %s is missing!\n", gold_module->cells_.at(cell->name)->parameters[ID::NAME].decode_string().c_str());
	// RTLIL::Wire *gold_state_wire = gold_module->addWire("\\injection_state", gold_state->width);
	// gold_state_wire->port_output = true;
	// gold_module->fixup_ports();
	// gold_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gold_state_wire), gold_sigmap(RTLIL::SigSpec(gold_state))));

	// Setup gate module
	RTLIL::Module *gate_module = module->clone();
	gate_module->name = "\\gate_" + module->name.str().substr(1);
	miter_design->add(gate_module);

	corrupt_transition(fsm_data, transition);
	fsm_data.copy_to_cell(gate_module->cells_.at(cell->name));

	RTLIL::SigSpec gate_input = gate_module->cells_.at(cell->name)->getPort(ID::CTRL_IN);

	Pass::call(miter_design, "fsm_map");

	RTLIL::Wire *gate_state;
	RTLIL::SigSpec gate_observables;
	SigMap gate_sigmap(gate_module);

	for (auto observable : observables) {
		RTLIL::Wire *observable_wire = gate_module->wire("\\" + observable);
		if (!observable_wire) log_cmd_error("Observable %s is missing!\n", observable.c_str());
		gate_observables.append(observable_wire);
	}
	RTLIL::Wire *gate_observables_wire = gate_module->addWire("\\injection_observables", gate_observables.size());
	gate_observables_wire->port_output = true;
	gate_module->fixup_ports();
	gate_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gate_observables_wire), gate_sigmap(gate_observables)));

	RTLIL::Wire *gate_input_wire = gate_module->addWire("\\injection_input", gate_input.size());
	gate_input_wire->port_output = true;
	gate_module->fixup_ports();
	gate_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gate_input_wire), gate_sigmap(gate_input)));

	gate_state = gate_module->wire(cell->parameters[ID::NAME].decode_string());
	if (!gate_state) log_cmd_error("State %s is missing!\n", gate_module->cells_.at(cell->name)->parameters[ID::NAME].decode_string().c_str());
	RTLIL::Wire *gate_state_wire = gate_module->addWire("\\injection_state", gate_state->width);
	gate_state_wire->port_output = true;
	gate_module->fixup_ports();
	gate_module->connect(RTLIL::SigSig(RTLIL::SigSpec(gate_state_wire), gate_sigmap(RTLIL::SigSpec(gate_state))));
	
	log("Creating miter cell \"%s\" with gold cell \"%s\" and gate cell \"%s\".\n", RTLIL::id2cstr(miter_module->name), RTLIL::id2cstr(gold_module->name), RTLIL::id2cstr(gate_module->name));

	RTLIL::Cell *gold_cell = miter_module->addCell(ID(gold), gold_module->name);
	RTLIL::Cell *gate_cell = miter_module->addCell(ID(gate), gate_module->name);

	RTLIL::SigSpec all_conditions;

	for (auto gold_wire : gate_module->wires())
	{
		if (gold_wire->port_input)
		{
			RTLIL::Wire *w = miter_module->addWire("\\in_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w->port_input = true;

			gold_cell->setPort(gold_wire->name, w);
			gate_cell->setPort(gold_wire->name, w);
		}

		if (gold_wire->name.str() == "\\injection_observables")
		{
			RTLIL::Wire *w_gold = miter_module->addWire("\\gold_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w_gold->port_output = true;
			RTLIL::Wire *w_gate = miter_module->addWire("\\gate_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w_gate->port_output = true;

			gold_cell->setPort(gold_wire->name, w_gold);
			gate_cell->setPort(gold_wire->name, w_gate);
		}

		if (gold_wire->name.str() == "\\injection_state" || gold_wire->name.str() == "\\injection_input")
		{
			// RTLIL::Wire *w_gold = miter_module->addWire("\\gold_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			// w_gold->port_output = true;
			RTLIL::Wire *w_gate = miter_module->addWire("\\gate_" + RTLIL::unescape_id(gold_wire->name), gold_wire->width);
			w_gate->port_output = true;

			// gold_cell->setPort(gold_wire->name, w_gold);
			gate_cell->setPort(gold_wire->name, w_gate);
		}
	}

	miter_module->fixup_ports();

	Pass::call(miter_design, "hierarchy -check -top " + miter_module->name.str());
	Pass::call(miter_design, "flatten");
	Pass::call(miter_design, "opt -full -fine");
	Pass::call(miter_design, "wreduce");
	Pass::call(miter_design, "peepopt");
	Pass::call(miter_design, "opt_clean");
	Pass::call(miter_design, "share");
	Pass::call(miter_design, "opt -full -fine");
	Pass::call(miter_design, "memory -nomap");
	Pass::call(miter_design, "opt_clean");
	Pass::call(miter_design, "opt -full -fine");
	Pass::call(miter_design, "memory_map");
	Pass::call(miter_design, "opt -full -fine");
	Pass::call(miter_design, "clk2fflogic");
	Pass::call(miter_design, "opt -full -fine");

	return miter_design;
}

struct InjectFsmPass : public Pass {
	InjectFsmPass() : Pass("inject_fsm", "inject bugs into the FSMs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::vector<std::pair<std::string, std::string>> sets, sets_init;
		std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
		std::map<int, std::vector<std::string>> unsets_at;
		std::vector<std::string> shows;
		std::vector<std::string> observables;
		int maxsteps = 24, initsteps = 0, timeout = 0, stepsize = 1;
		bool set_init_zero = false, show_inputs = false, show_outputs = false;

		log_header(design, "Executing InjectFSM pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-timeout" && argidx+1 < args.size()) {
				timeout = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-maxsteps" && argidx+1 < args.size()) {
				maxsteps = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-initsteps" && argidx+1 < args.size()) {
				initsteps = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-stepsize" && argidx+1 < args.size()) {
				stepsize = max(1, atoi(args[++argidx].c_str()));
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-at" && argidx+3 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets_at[timestep].push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-unset-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				unsets_at[timestep].push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-set-init" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets_init.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-init-zero") {
				set_init_zero = true;
				continue;
			}
			if (args[argidx] == "-show" && argidx+1 < args.size()) {
				shows.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-show-inputs") {
				show_inputs = true;
				continue;
			}
			if (args[argidx] == "-show-outputs") {
				show_outputs = true;
				continue;
			}
			if (args[argidx] == "-observable" && argidx+1 < args.size()) {
				observables.push_back(args[++argidx]);
				continue;
			}
		}

		// TODO expand FSMs
		// Pass::call(design, "fsm_detect -ignore-good-state-reg -ignore-init-attr -ignore-module-port -ignore-self-reset");
		Pass::call(design, "fsm_detect");
		Pass::call(design, "fsm_extract");
		// Pass::call(design, "fsm_info");

		Pass::call(design, "fsm_opt");
		Pass::call(design, "opt_clean");
		Pass::call(design, "fsm_opt");
		
		// Pass::call(design, "fsm_expand");
		// Pass::call(design, "fsm_opt");
		// Pass::call(design, "opt_clean");
		// Pass::call(design, "fsm_opt");
		// Pass::call(design, "fsm_info");

		for (auto module : design->selected_modules()) {
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($fsm)) {
					FsmData fsm_data;
					fsm_data.copy_from_cell(cell);

					for (auto &transition : fsm_data.transition_table){
						if(is_challenging(transition)){
							FsmData::transition_t transition_copy = transition;

							RTLIL::Design *miter_design = create_miter(module, cell, fsm_data, transition, observables);
							RTLIL::Module *miter_mod = miter_design->module("\\miter_" + module->name.str().substr(1));

							shows.clear();
							if (show_inputs) {
								for (auto &it : miter_mod->wires_)
									if (it.second->port_input)
										shows.push_back(it.second->name.str());
							}
							if (show_outputs) {
								for (auto &it : miter_mod->wires_)
									if (it.second->port_output)
										shows.push_back(it.second->name.str());
							}

							// TODO check out enable undef (speedup?)
							SatHelper sathelper(miter_design, miter_mod, false, false);
							sathelper.sets = sets;
							sathelper.sets_at = sets_at;
							sathelper.unsets_at = unsets_at;
							sathelper.shows = shows;
							sathelper.timeout = timeout;
							sathelper.sets_init = sets_init;
							sathelper.set_init_zero = set_init_zero;

							RTLIL::SigSpec fsm_lhs, fsm_rhs;

							RTLIL::Wire *state_wire = miter_mod->wire("\\gate_injection_state");
							if (!state_wire) log_cmd_error("State port is missing!\n");
							fsm_lhs.append(state_wire);
							fsm_rhs.append(fsm_data.state_table.at(transition.state_in));
							if (fsm_lhs.size() != fsm_rhs.size())
								log_cmd_error("State expression with different lhs and rhs sizes.\n");

							RTLIL::Wire *input_wire = miter_mod->wire("\\gate_injection_input");
							if (!input_wire) log_cmd_error("Input port is missing!\n");
							fsm_lhs.append(input_wire);
							fsm_rhs.append(transition.ctrl_in);
							if (fsm_lhs.size() != fsm_rhs.size())
								log_cmd_error("Input expression with different lhs and rhs sizes.\n");

							for(int sensitization_step = 1; sensitization_step <= maxsteps; sensitization_step++){
								log("Sensitizing.\n");
								sathelper.setup(sensitization_step, sensitization_step == 1);
								sathelper.generate_model();
								log_flush();

								if (sathelper.solve(sathelper.satgen.signals_eq(fsm_lhs, fsm_rhs, sensitization_step))){
									log("Sensitized the bug.\n");
									sathelper.print_model();
									log_flush();
									
									std::vector<int> clause;

									// TODO possibly wrong check invalidate_model
									for (size_t i = 0; i < sathelper.modelExpressions.size(); i++)
										clause.push_back(sathelper.modelValues.at(i) ? sathelper.modelExpressions.at(i) : sathelper.ez->NOT(sathelper.modelExpressions.at(i)));
									sathelper.ez->assume(sathelper.ez->expression(ezSAT::OpAnd, clause));

									RTLIL::Wire *gold_observables_wire = miter_mod->wire("\\gold_injection_observables");
									if (!gold_observables_wire) log_cmd_error("Gold observables port is missing!\n");
									RTLIL::Wire *gate_observables_wire = miter_mod->wire("\\gate_injection_observables");
									if (!gate_observables_wire) log_cmd_error("Gate observables port is missing!\n");
									RTLIL::SigSpec observables_lhs(gold_observables_wire), observables_rhs(gate_observables_wire);
									if (observables_lhs.size() != observables_rhs.size())
										log_cmd_error("Observables expression with different lhs and rhs sizes.\n");

									for(int propagation_step = sensitization_step + 1; propagation_step <= maxsteps; ++propagation_step){
										log("Propagating.\n");
										sathelper.setup(propagation_step, propagation_step == 1);
										sathelper.generate_model();
										log_flush();

										if(sathelper.solve(sathelper.ez->NOT(sathelper.satgen.signals_eq(observables_lhs, observables_rhs, propagation_step)))){
											log("Propagated the bug.\n");
											sathelper.print_model();
											goto found_pov;
										}
									}
								}
							}

							transition = transition_copy;
							found_pov:
							;
							// TODO check whether deleting this is necessary because it causes problems
							// delete miter_design;
							break;
						}
					}
					// TODO bugs interfere with each other due to the loose placeholder is challenging condition
					// uncomment later
					// fsm_data.copy_to_cell(cell);
				}
			}
		}
		log("Done injecting!\n");
		Pass::call(design, "fsm_info");
		Pass::call(design, "fsm_map");
	}
} InjectFsmPass;

PRIVATE_NAMESPACE_END
