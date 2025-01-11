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

struct VerifyMiterPass : public Pass {
	VerifyMiterPass() : Pass("verify_miter", "verify signal mix-up bugs") { }
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
		int max_sensitization = 20, max_propagation = 32, initsteps = 0, timeout = 0, stepsize = 1;
		bool set_init_zero = false, show_inputs = false, show_outputs = false;

		log_header(design, "Executing VerifyMiterPass pass.\n");

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
		}

		Pass::call(design, "memory_map");
		Pass::call(design, "opt -full");
		Pass::call(design, "clk2fflogic");
		Pass::call(design, "opt -full -fine");


    RTLIL::Module *miter_module = design->module("\\miter");

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

            if (sathelper.solve(sathelper.ez->NOT(sathelper.satgen.signals_eq(host_output, reference_output, sensitization_step)))){

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
					// sathelper.
					// sathelper.ez->printDIMACS()
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
} VerifyMiterPass;

PRIVATE_NAMESPACE_END