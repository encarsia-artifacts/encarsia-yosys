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

#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/satgen.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <errno.h>
#include <string.h>
#include "selection.h"
#include <chrono>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static std::string get_time(){
	auto now = std::chrono::system_clock::now();
	auto milliseconds = std::chrono::duration_cast<std::chrono::milliseconds>(now.time_since_epoch()) % 1000;
	std::time_t now_time_t = std::chrono::system_clock::to_time_t(now);
	char buf[100];
    std::strftime(buf, sizeof(buf), "%Y-%m-%d %H:%M:%S", std::localtime(&now_time_t));

	return std::string(buf)+"."+std::to_string(milliseconds.count());
}

static void synthetize_miter(RTLIL::Design *design, std::string top_module)
{
	Pass::call(design, "inject_map");
	Pass::call(design, "opt");
	Pass::call(design, "hierarchy -check -top " + top_module);
	Pass::call(design, "flatten");
	Pass::call(design, "opt");
	Pass::call(design, "wreduce");
	Pass::call(design, "peepopt");
	Pass::call(design, "opt_clean");
	// TODO check whether this can be removed
	Pass::call(design, "memory -nomap");
	Pass::call(design, "opt_clean");
	Pass::call(design, "opt -fast -full");
	Pass::call(design, "memory_map");
	Pass::call(design, "opt -full");
	Pass::call(design, "clk2fflogic");
	Pass::call(design, "opt -full -fine");
}

// TODO take care of inconsistent naming cell/amt
static RTLIL::Module *create_miter(RTLIL::Design *design, RTLIL::Module *host_module, RTLIL::Cell *host_amt, RTLIL::Module *reference_module, RTLIL::Cell *reference_amt, std::vector<std::string> &observables)
{
	SigMap host_sigmap(host_module);
	RTLIL::SigSpec host_select = host_amt->getPort(ID::S);
	RTLIL::SigSpec host_output = host_amt->getPort(ID::Y);
	RTLIL::SigSpec host_observables;

    // TODO names might conflict with preexisting signals
    // TODO sigmap might be unnecessary remove
    RTLIL::Wire *host_select_port = host_module->addWire("\\select", host_select.size());
    host_select_port->port_output = true;
	host_module->connect(RTLIL::SigSig(host_select_port, host_sigmap(host_select)));

    RTLIL::Wire *host_output_port = host_module->addWire("\\output", host_output.size());
    host_output_port->port_output = true;
	host_module->connect(RTLIL::SigSig(host_output_port, host_sigmap(host_output)));

    for (auto observable : observables) {
		RTLIL::Wire *observable_wire = host_module->wire("\\" + observable);
		if (!observable_wire) log_cmd_error("Observable %s is missing!\n", observable.c_str());
		host_observables.append(observable_wire);
	}
    RTLIL::Wire *host_observables_port = host_module->addWire("\\observables", host_observables.size());
    host_observables_port->port_output = true;
	host_module->connect(RTLIL::SigSig(host_observables_port, host_sigmap(host_observables)));

	host_module->fixup_ports();



	SigMap reference_sigmap(reference_module);
	RTLIL::SigSpec reference_select = reference_amt->getPort(ID::S);
	RTLIL::SigSpec reference_output = reference_amt->getPort(ID::Y);
	RTLIL::SigSpec reference_observables;

    RTLIL::Wire *reference_select_port = reference_module->addWire("\\select", reference_select.size());
    reference_select_port->port_output = true;
	reference_module->connect(RTLIL::SigSig(reference_select_port, reference_sigmap(reference_select)));

    RTLIL::Wire *reference_output_port = reference_module->addWire("\\output", reference_output.size());
    reference_output_port->port_output = true;
	reference_module->connect(RTLIL::SigSig(reference_output_port, reference_sigmap(reference_output)));

    for (auto observable : observables) {
		RTLIL::Wire *observable_wire = reference_module->wire("\\" + observable);
		if (!observable_wire) log_cmd_error("Observable %s is missing!\n", observable.c_str());
		reference_observables.append(observable_wire);
	}
    RTLIL::Wire *reference_observables_port = reference_module->addWire("\\observables", reference_observables.size());
    reference_observables_port->port_output = true;
	reference_module->connect(RTLIL::SigSig(reference_observables_port, reference_sigmap(reference_observables)));

	reference_module->fixup_ports();



    RTLIL::Module *miter_module = new RTLIL::Module;
	miter_module->name = "\\miter";
	design->add(miter_module);
    RTLIL::Cell *host_cell = miter_module->addCell(ID(host), host_module->name);
    RTLIL::Cell *reference_cell = miter_module->addCell(ID(reference), reference_module->name);

	for (auto host_wire : host_module->wires())
	{
		if (host_wire->port_input)
		{
			RTLIL::Wire *w = miter_module->addWire("\\in_" + RTLIL::unescape_id(host_wire->name), host_wire->width);
			w->port_input = true;

			host_cell->setPort(host_wire->name, w);
			reference_cell->setPort(host_wire->name, w);
		}

		if (host_wire->name.str() == "\\select" || host_wire->name.str() == "\\output" || host_wire->name.str() == "\\observables")
		{
			RTLIL::Wire *w_host = miter_module->addWire("\\host_" + RTLIL::unescape_id(host_wire->name), host_wire->width);
			w_host->port_output = true;
			RTLIL::Wire *w_reference = miter_module->addWire("\\reference_" + RTLIL::unescape_id(host_wire->name), host_wire->width);
			w_reference->port_output = true;

			host_cell->setPort(host_wire->name, w_host);
			reference_cell->setPort(host_wire->name, w_reference);
		}
	}

	miter_module->fixup_ports();

	return miter_module;
}

struct InjectVerifyPass : public Pass {
	InjectVerifyPass() : Pass("inject_verify", "inject bugs into the AMTs") { }
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
		int max_sensitization = 20, max_propagation = 32, initsteps = 0, timeout = 0, stepsize = 1;
		bool set_init_zero = false, show_inputs = false, show_outputs = false;

		log_header(design, "Executing InjectVerify pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-timeout" && argidx+1 < args.size()) {
				timeout = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-sensitization" && argidx+1 < args.size()) {
				max_sensitization = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max-propagation" && argidx+1 < args.size()) {
				max_propagation = atoi(args[++argidx].c_str());
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

        RTLIL::Module *host_module = design->module("\\host");
        if (!host_module) {
            log_error("Can not find host module in current design!\n");
        }
        RTLIL::Module *reference_module = design->module("\\reference");
        if (!reference_module) {
            log_error("Can not find reference module in current design!\n");
        }

        RTLIL::Cell *host_cell;
        RTLIL::Cell *reference_cell;
        for (RTLIL::Cell *cell : host_module->selected_cells()) {
            if (!cell->attributes.count(ID(buggy))) continue;

            host_cell = cell;
            reference_cell = reference_module->cell(cell->name);
            if (!reference_cell) {
                log_error("Can not find buggy cell in reference module!\n");
            }

            // TODO eventually implement multiple buggy cells
            break;
        }
		if (!host_cell) {
			log_error("Can not find buggy cell in host module!\n");
		}

        // TODO this might not work because output signals might be deleted maybe
        std::vector<selection_t> host_selections, reference_selections;
        copy_from_cell(host_cell, host_selections);
        copy_from_cell(reference_cell, reference_selections);
		// TODO whenever table simplification is added
		if (host_selections.size() != reference_selections.size()) {
			log_error("Selection table sizes do not match!\n");
		}

        RTLIL::Module *miter_module = create_miter(design, host_module, host_cell, reference_module, reference_cell, observables);
        synthetize_miter(design, miter_module->name.str());





		shows.clear();
		if (show_inputs) {
			for (auto &it : miter_module->wires_)
				if (it.second->port_input)
					shows.push_back(it.second->name.str());
		}
		if (show_outputs) {
			for (auto &it : miter_module->wires_)
				if (it.second->port_output)
					shows.push_back(it.second->name.str());
		}

        SatHelper sathelper(design, miter_module, false, false);
        // SatHelper sathelper(miter_design, miter_mod, true, false);
        sathelper.sets = sets;
        sathelper.sets_at = sets_at;
        sathelper.unsets_at = unsets_at;
        sathelper.shows = shows;
        sathelper.timeout = timeout;
        sathelper.sets_init = sets_init;
        sathelper.set_init_zero = set_init_zero;

		// TODO actually create the condition
        RTLIL::Wire *select_port = miter_module->wire("\\host_select");
        if (!select_port) log_cmd_error("Select port is missing!\n");
		std::vector<RTLIL::SigSig> selects;
		for (size_t i = 0; i < host_selections.size(); ++i) {
			if (!host_selections.at(i).buggy) continue;
			RTLIL::SigSpec select_circuit, select_selection;

			for (size_t j = 0; j < host_selections.at(i).select.bits.size(); j++){
				if (host_selections.at(i).select.bits.at(j) == RTLIL::State::S0 || host_selections.at(i).select.bits.at(j) == RTLIL::State::S1) {
					select_circuit.append(RTLIL::SigSpec(select_port, j));
					select_selection.append(host_selections.at(i).select.bits.at(j));
				}
			}
			selects.push_back(RTLIL::SigSig(select_circuit, select_selection));
			log("found select: %s=%s\n", log_signal(select_circuit), log_signal(select_selection));
		}

        RTLIL::Wire *host_output_port = miter_module->wire("\\host_output");
        if (!host_output_port) log_cmd_error("Host output port is missing!\n");
        RTLIL::Wire *reference_output_port = miter_module->wire("\\reference_output");
        if (!reference_output_port) log_cmd_error("Reference output port is missing!\n");
        RTLIL::SigSpec host_output(host_output_port), reference_output(reference_output_port);
        if (host_output.size() != reference_output.size())
            log_cmd_error("Output expression with different lhs and rhs sizes.\n");

        RTLIL::Wire *host_observables_port = miter_module->wire("\\host_observables");
        if (!host_observables_port) log_cmd_error("Host observables port is missing!\n");
        RTLIL::Wire *reference_observables_port = miter_module->wire("\\reference_observables");
        if (!reference_observables_port) log_cmd_error("Reference observables port is missing!\n");
        RTLIL::SigSpec host_observables(host_observables_port), reference_observables(reference_observables_port);
        if (host_observables.size() != reference_observables.size())
            log_cmd_error("Observables expression with different lhs and rhs sizes.\n");

		log("Sensitizing the bug!\n");
		log("time: %s\n", get_time().c_str());
		log_flush();
        for(int sensitization_step = 1; sensitization_step <= max_sensitization; sensitization_step++){
            sathelper.setup(sensitization_step, sensitization_step == 1);
            sathelper.generate_model();
            log_flush();

            // TODO maybe implement steps of size > 1

			// TODO maybe check whether this could be done in a smarter way
			std::vector<int> clause;
			for (auto select : selects) {
				clause.push_back(sathelper.satgen.signals_eq(select.first, select.second, sensitization_step));
			}

            // if (sathelper.solve(sathelper.ez->expression(ezSAT::OpOr, clause))){
            if (sathelper.solve(sathelper.ez->AND(sathelper.ez->expression(ezSAT::OpOr, clause), sathelper.ez->NOT(sathelper.satgen.signals_eq(host_output, reference_output, sensitization_step))))){
                // sathelper.ez->assume(sathelper.ez->AND(sathelper.satgen.signals_eq(select_circuit, select_selection, sensitization_step), sathelper.ez->NOT(sathelper.satgen.signals_eq(output_lhs, output_rhs, sensitization_step))));
                // sathelper.maximize_undefs();

                log("Sensitized the bug.\n");
				log("time: %s\n", get_time().c_str());
                log_flush();
                sathelper.print_model();
                log_flush();

                // TODO possibly wrong check invalidate_model
                // TODO check whether this also sets dont cares!!!!
                for (size_t i = 0; i < sathelper.modelExpressions.size(); i++)
                    sathelper.ez->assume(sathelper.modelValues.at(i) ? sathelper.modelExpressions.at(i) : sathelper.ez->NOT(sathelper.modelExpressions.at(i)));


                for(int propagation_step = sensitization_step + 1; propagation_step <= max_propagation; ++propagation_step){
                    sathelper.setup(propagation_step, propagation_step == 1);
                    sathelper.generate_model();
                    log_flush();

                    // TODO maybe implement steps of size > 1

                    // TODO beter logs
                    if(sathelper.solve(sathelper.ez->NOT(sathelper.satgen.signals_eq(host_observables, reference_observables, propagation_step)))){
                        log("Propagated the bug.\n");
						log("time: %s\n", get_time().c_str());
						log_flush();
                        sathelper.print_model();
                        log_flush();
                        break;
                    } else if (sathelper.gotTimeout) {
                        log("Timed out.\n");
						log("time: %s\n", get_time().c_str());
                        log_flush();
                        break;
                    }
                }

                // Exit outer sat loop
                sensitization_step += max_sensitization;
            } else if (sathelper.gotTimeout) {
                log("Timed out.\n");
				log("time: %s\n", get_time().c_str());
                log_flush();
                break;
            } else if (sensitization_step == max_sensitization) {
                log("Failed to sensitize the bug.\n");
				log("time: %s\n", get_time().c_str());
                log_flush();
            }
        }
	}
} InjectVerifyPass;

PRIVATE_NAMESPACE_END