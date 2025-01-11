/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

// [[CITE]] Temporal Induction by Incremental SAT Solving
// Niklas Een and Niklas Sörensson (2003)
// http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.4.8161

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/consteval.h"
#include "kernel/sigtools.h"
#include "kernel/log.h"
#include "kernel/satgen.h"
#include <stdlib.h>
#include <stdio.h>
#include <algorithm>
#include <errno.h>
#include <string.h>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void print_proof_failed()
{
	log("\n");
	log("   ______                   ___       ___       _ _            _ _ \n");
	log("  (_____ \\                 / __)     / __)     (_) |          | | |\n");
	log("   _____) )___ ___   ___ _| |__    _| |__ _____ _| | _____  __| | |\n");
	log("  |  ____/ ___) _ \\ / _ (_   __)  (_   __|____ | | || ___ |/ _  |_|\n");
	log("  | |   | |  | |_| | |_| || |       | |  / ___ | | || ____( (_| |_ \n");
	log("  |_|   |_|   \\___/ \\___/ |_|       |_|  \\_____|_|\\_)_____)\\____|_|\n");
	log("\n");
}

void print_timeout()
{
	log("\n");
	log("        _____  _  _      _____ ____  _     _____\n");
	log("       /__ __\\/ \\/ \\__/|/  __//  _ \\/ \\ /\\/__ __\\\n");
	log("         / \\  | || |\\/|||  \\  | / \\|| | ||  / \\\n");
	log("         | |  | || |  |||  /_ | \\_/|| \\_/|  | |\n");
	log("         \\_/  \\_/\\_/  \\|\\____\\\\____/\\____/  \\_/\n");
	log("\n");
}

void print_qed()
{
	log("\n");
	log("                  /$$$$$$      /$$$$$$$$     /$$$$$$$    \n");
	log("                 /$$__  $$    | $$_____/    | $$__  $$   \n");
	log("                | $$  \\ $$    | $$          | $$  \\ $$   \n");
	log("                | $$  | $$    | $$$$$       | $$  | $$   \n");
	log("                | $$  | $$    | $$__/       | $$  | $$   \n");
	log("                | $$/$$ $$    | $$          | $$  | $$   \n");
	log("                |  $$$$$$/ /$$| $$$$$$$$ /$$| $$$$$$$//$$\n");
	log("                 \\____ $$$|__/|________/|__/|_______/|__/\n");
	log("                       \\__/                              \n");
	log("\n");
}

struct SatPass : public Pass {
	SatPass() : Pass("sat", "solve a SAT problem in the circuit") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sat [options] [selection]\n");
		log("\n");
		log("This command solves a SAT problem defined over the currently selected circuit\n");
		log("and additional constraints passed as parameters.\n");
		log("\n");
		log("    -all\n");
		log("        show all solutions to the problem (this can grow exponentially, use\n");
		log("        -max <N> instead to get <N> solutions)\n");
		log("\n");
		log("    -max <N>\n");
		log("        like -all, but limit number of solutions to <N>\n");
		log("\n");
		log("    -enable_undef\n");
		log("        enable modeling of undef value (aka 'x-bits')\n");
		log("        this option is implied by -set-def, -set-undef et. cetera\n");
		log("\n");
		log("    -max_undef\n");
		log("        maximize the number of undef bits in solutions, giving a better\n");
		log("        picture of which input bits are actually vital to the solution.\n");
		log("\n");
		log("    -set <signal> <value>\n");
		log("        set the specified signal to the specified value.\n");
		log("\n");
		log("    -set-def <signal>\n");
		log("        add a constraint that all bits of the given signal must be defined\n");
		log("\n");
		log("    -set-any-undef <signal>\n");
		log("        add a constraint that at least one bit of the given signal is undefined\n");
		log("\n");
		log("    -set-all-undef <signal>\n");
		log("        add a constraint that all bits of the given signal are undefined\n");
		log("\n");
		log("    -set-def-inputs\n");
		log("        add -set-def constraints for all module inputs\n");
		log("\n");
		log("    -set-def-formal\n");
		log("        add -set-def constraints for formal $anyinit, $anyconst, $anyseq cells\n");
		log("\n");
		log("    -show <signal>\n");
		log("        show the model for the specified signal. if no -show option is\n");
		log("        passed then a set of signals to be shown is automatically selected.\n");
		log("\n");
		log("    -show-inputs, -show-outputs, -show-ports\n");
		log("        add all module (input/output) ports to the list of shown signals\n");
		log("\n");
		log("    -show-regs, -show-public, -show-all\n");
		log("        show all registers, show signals with 'public' names, show all signals\n");
		log("\n");
		log("    -ignore_div_by_zero\n");
		log("        ignore all solutions that involve a division by zero\n");
		log("\n");
		log("    -ignore_unknown_cells\n");
		log("        ignore all cells that can not be matched to a SAT model\n");
		log("\n");
		log("The following options can be used to set up a sequential problem:\n");
		log("\n");
		log("    -seq <N>\n");
		log("        set up a sequential problem with <N> time steps. The steps will\n");
		log("        be numbered from 1 to N.\n");
		log("\n");
		log("        note: for large <N> it can be significantly faster to use\n");
		log("        -tempinduct-baseonly -maxsteps <N> instead of -seq <N>.\n");
		log("\n");
		log("    -set-at <N> <signal> <value>\n");
		log("    -unset-at <N> <signal>\n");
		log("        set or unset the specified signal to the specified value in the\n");
		log("        given timestep. this has priority over a -set for the same signal.\n");
		log("\n");
		log("    -set-assumes\n");
		log("        set all assumptions provided via $assume cells\n");
		log("\n");
		log("    -set-def-at <N> <signal>\n");
		log("    -set-any-undef-at <N> <signal>\n");
		log("    -set-all-undef-at <N> <signal>\n");
		log("        add undef constraints in the given timestep.\n");
		log("\n");
		log("    -set-init <signal> <value>\n");
		log("        set the initial value for the register driving the signal to the value\n");
		log("\n");
		log("    -set-init-undef\n");
		log("        set all initial states (not set using -set-init) to undef\n");
		log("\n");
		log("    -set-init-def\n");
		log("        do not force a value for the initial state but do not allow undef\n");
		log("\n");
		log("    -set-init-zero\n");
		log("        set all initial states (not set using -set-init) to zero\n");
		log("\n");
		log("    -dump_vcd <vcd-file-name>\n");
		log("        dump SAT model (counter example in proof) to VCD file\n");
		log("\n");
		log("    -dump_json <json-file-name>\n");
		log("        dump SAT model (counter example in proof) to a WaveJSON file.\n");
		log("\n");
		log("    -dump_cnf <cnf-file-name>\n");
		log("        dump CNF of SAT problem (in DIMACS format). in temporal induction\n");
		log("        proofs this is the CNF of the first induction step.\n");
		log("\n");
		log("The following additional options can be used to set up a proof. If also -seq\n");
		log("is passed, a temporal induction proof is performed.\n");
		log("\n");
		log("    -tempinduct\n");
		log("        Perform a temporal induction proof. In a temporal induction proof it is\n");
		log("        proven that the condition holds forever after the number of time steps\n");
		log("        specified using -seq.\n");
		log("\n");
		log("    -tempinduct-def\n");
		log("        Perform a temporal induction proof. Assume an initial state with all\n");
		log("        registers set to defined values for the induction step.\n");
		log("\n");
		log("    -tempinduct-baseonly\n");
		log("        Run only the basecase half of temporal induction (requires -maxsteps)\n");
		log("\n");
		log("    -tempinduct-inductonly\n");
		log("        Run only the induction half of temporal induction\n");
		log("\n");
		log("    -tempinduct-skip <N>\n");
		log("        Skip the first <N> steps of the induction proof.\n");
		log("\n");
		log("        note: this will assume that the base case holds for <N> steps.\n");
		log("        this must be proven independently with \"-tempinduct-baseonly\n");
		log("        -maxsteps <N>\". Use -initsteps if you just want to set a\n");
		log("        minimal induction length.\n");
		log("\n");
		log("    -prove <signal> <value>\n");
		log("        Attempt to proof that <signal> is always <value>.\n");
		log("\n");
		log("    -prove-x <signal> <value>\n");
		log("        Like -prove, but an undef (x) bit in the lhs matches any value on\n");
		log("        the right hand side. Useful for equivalence checking.\n");
		log("\n");
		log("    -prove-asserts\n");
		log("        Prove that all asserts in the design hold.\n");
		log("\n");
		log("    -prove-skip <N>\n");
		log("        Do not enforce the prove-condition for the first <N> time steps.\n");
		log("\n");
		log("    -maxsteps <N>\n");
		log("        Set a maximum length for the induction.\n");
		log("\n");
		log("    -initsteps <N>\n");
		log("        Set initial length for the induction.\n");
		log("        This will speed up the search of the right induction length\n");
		log("        for deep induction proofs.\n");
		log("\n");
		log("    -stepsize <N>\n");
		log("        Increase the size of the induction proof in steps of <N>.\n");
		log("        This will speed up the search of the right induction length\n");
		log("        for deep induction proofs.\n");
		log("\n");
		log("    -timeout <N>\n");
		log("        Maximum number of seconds a single SAT instance may take.\n");
		log("\n");
		log("    -verify\n");
		log("        Return an error and stop the synthesis script if the proof fails.\n");
		log("\n");
		log("    -verify-no-timeout\n");
		log("        Like -verify but do not return an error for timeouts.\n");
		log("\n");
		log("    -falsify\n");
		log("        Return an error and stop the synthesis script if the proof succeeds.\n");
		log("\n");
		log("    -falsify-no-timeout\n");
		log("        Like -falsify but do not return an error for timeouts.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::vector<std::pair<std::string, std::string>> sets, sets_init, prove, prove_x;
		std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
		std::map<int, std::vector<std::string>> unsets_at, sets_def_at, sets_any_undef_at, sets_all_undef_at;
		std::vector<std::string> shows, sets_def, sets_any_undef, sets_all_undef;
		int loopcount = 0, seq_len = 0, maxsteps = 0, initsteps = 0, timeout = 0, prove_skip = 0;
		bool verify = false, fail_on_timeout = false, enable_undef = false, set_def_inputs = false, set_def_formal = false;
		bool ignore_div_by_zero = false, set_init_undef = false, set_init_zero = false, max_undef = false;
		bool tempinduct = false, prove_asserts = false, show_inputs = false, show_outputs = false;
		bool show_regs = false, show_public = false, show_all = false;
		bool ignore_unknown_cells = false, falsify = false, tempinduct_def = false, set_init_def = false;
		bool tempinduct_baseonly = false, tempinduct_inductonly = false, set_assumes = false;
		int tempinduct_skip = 0, stepsize = 1;
		std::string vcd_file_name, json_file_name, cnf_file_name;

		log_header(design, "Executing SAT pass (solving SAT problems in the circuit).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-all") {
				loopcount = -1;
				continue;
			}
			if (args[argidx] == "-verify") {
				fail_on_timeout = true;
				verify = true;
				continue;
			}
			if (args[argidx] == "-verify-no-timeout") {
				verify = true;
				continue;
			}
			if (args[argidx] == "-falsify") {
				fail_on_timeout = true;
				falsify = true;
				continue;
			}
			if (args[argidx] == "-falsify-no-timeout") {
				falsify = true;
				continue;
			}
			if (args[argidx] == "-timeout" && argidx+1 < args.size()) {
				timeout = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-max" && argidx+1 < args.size()) {
				loopcount = atoi(args[++argidx].c_str());
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
			if (args[argidx] == "-ignore_div_by_zero") {
				ignore_div_by_zero = true;
				continue;
			}
			if (args[argidx] == "-enable_undef") {
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-max_undef") {
				enable_undef = true;
				max_undef = true;
				continue;
			}
			if (args[argidx] == "-set-def-inputs") {
				enable_undef = true;
				set_def_inputs = true;
				continue;
			}
			if (args[argidx] == "-set-def-formal") {
				enable_undef = true;
				set_def_formal = true;
				continue;
			}
			if (args[argidx] == "-set" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-def" && argidx+1 < args.size()) {
				sets_def.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-any-undef" && argidx+1 < args.size()) {
				sets_any_undef.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-all-undef" && argidx+1 < args.size()) {
				sets_all_undef.push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-assumes") {
				set_assumes = true;
				continue;
			}
			if (args[argidx] == "-tempinduct") {
				tempinduct = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-def") {
				tempinduct = true;
				tempinduct_def = true;
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-baseonly") {
				tempinduct = true;
				tempinduct_baseonly = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-inductonly") {
				tempinduct = true;
				tempinduct_inductonly = true;
				continue;
			}
			if (args[argidx] == "-tempinduct-skip" && argidx+1 < args.size()) {
				tempinduct_skip = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-prove" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				prove.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-prove-x" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				prove_x.push_back(std::pair<std::string, std::string>(lhs, rhs));
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-prove-asserts") {
				prove_asserts = true;
				continue;
			}
			if (args[argidx] == "-prove-skip" && argidx+1 < args.size()) {
				prove_skip = atoi(args[++argidx].c_str());
				continue;
			}
			if (args[argidx] == "-seq" && argidx+1 < args.size()) {
				seq_len = atoi(args[++argidx].c_str());
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
			if (args[argidx] == "-set-def-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_def_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-any-undef-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_any_undef_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-all-undef-at" && argidx+2 < args.size()) {
				int timestep = atoi(args[++argidx].c_str());
				sets_all_undef_at[timestep].push_back(args[++argidx]);
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-init" && argidx+2 < args.size()) {
				std::string lhs = args[++argidx];
				std::string rhs = args[++argidx];
				sets_init.push_back(std::pair<std::string, std::string>(lhs, rhs));
				continue;
			}
			if (args[argidx] == "-set-init-undef") {
				set_init_undef = true;
				enable_undef = true;
				continue;
			}
			if (args[argidx] == "-set-init-def") {
				set_init_def = true;
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
			if (args[argidx] == "-show-ports") {
				show_inputs = true;
				show_outputs = true;
				continue;
			}
			if (args[argidx] == "-show-regs") {
				show_regs = true;
				continue;
			}
			if (args[argidx] == "-show-public") {
				show_public = true;
				continue;
			}
			if (args[argidx] == "-show-all") {
				show_all = true;
				continue;
			}
			if (args[argidx] == "-ignore_unknown_cells") {
				ignore_unknown_cells = true;
				continue;
			}
			if (args[argidx] == "-dump_vcd" && argidx+1 < args.size()) {
				vcd_file_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dump_json" && argidx+1 < args.size()) {
				json_file_name = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dump_cnf" && argidx+1 < args.size()) {
				cnf_file_name = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		RTLIL::Module *module = NULL;
		for (auto mod : design->selected_modules()) {
			if (module)
				log_cmd_error("Only one module must be selected for the SAT pass! (selected: %s and %s)\n", log_id(module), log_id(mod));
			module = mod;
		}
		if (module == NULL)
			log_cmd_error("Can't perform SAT on an empty selection!\n");

		if (!prove.size() && !prove_x.size() && !prove_asserts && tempinduct)
			log_cmd_error("Got -tempinduct but nothing to prove!\n");

		if (prove_skip && tempinduct)
			log_cmd_error("Options -prove-skip and -tempinduct don't work with each other. Use -seq instead of -prove-skip.\n");

		if (prove_skip >= seq_len && prove_skip > 0)
			log_cmd_error("The value of -prove-skip must be smaller than the one of -seq.\n");

		if (set_init_undef + set_init_zero + set_init_def > 1)
			log_cmd_error("The options -set-init-undef, -set-init-def, and -set-init-zero are exclusive!\n");

		if (set_def_inputs) {
			for (auto &it : module->wires_)
				if (it.second->port_input)
					sets_def.push_back(it.second->name.str());
		}

		if (show_inputs) {
			for (auto &it : module->wires_)
				if (it.second->port_input)
					shows.push_back(it.second->name.str());
		}

		if (show_outputs) {
			for (auto &it : module->wires_)
				if (it.second->port_output)
					shows.push_back(it.second->name.str());
		}

		if (show_regs) {
			pool<Wire*> reg_wires;
			for (auto cell : module->cells()) {
				if (cell->type == ID($dff) || cell->type.begins_with("$_DFF_"))
					for (auto bit : cell->getPort(ID::Q))
						if (bit.wire)
							reg_wires.insert(bit.wire);
			}
			for (auto wire : reg_wires)
				shows.push_back(wire->name.str());
		}

		if (show_public) {
			for (auto wire : module->wires())
				if (wire->name.isPublic())
					shows.push_back(wire->name.str());
		}

		if (show_all) {
			for (auto wire : module->wires())
				shows.push_back(wire->name.str());
		}

		if (tempinduct)
		{
			if (loopcount > 0 || max_undef)
				log_cmd_error("The options -max, -all, and -max_undef are not supported for temporal induction proofs!\n");

			SatHelper basecase(design, module, enable_undef, set_def_formal);
			SatHelper inductstep(design, module, enable_undef, set_def_formal);

			basecase.sets = sets;
			basecase.set_assumes = set_assumes;
			basecase.prove = prove;
			basecase.prove_x = prove_x;
			basecase.prove_asserts = prove_asserts;
			basecase.sets_at = sets_at;
			basecase.unsets_at = unsets_at;
			basecase.shows = shows;
			basecase.timeout = timeout;
			basecase.sets_def = sets_def;
			basecase.sets_any_undef = sets_any_undef;
			basecase.sets_all_undef = sets_all_undef;
			basecase.sets_def_at = sets_def_at;
			basecase.sets_any_undef_at = sets_any_undef_at;
			basecase.sets_all_undef_at = sets_all_undef_at;
			basecase.sets_init = sets_init;
			basecase.set_init_def = set_init_def;
			basecase.set_init_undef = set_init_undef;
			basecase.set_init_zero = set_init_zero;
			basecase.satgen.ignore_div_by_zero = ignore_div_by_zero;
			basecase.ignore_unknown_cells = ignore_unknown_cells;

			for (int timestep = 1; timestep <= seq_len; timestep++)
				if (!tempinduct_inductonly)
					basecase.setup(timestep, timestep == 1);

			inductstep.sets = sets;
			inductstep.set_assumes = set_assumes;
			inductstep.prove = prove;
			inductstep.prove_x = prove_x;
			inductstep.prove_asserts = prove_asserts;
			inductstep.shows = shows;
			inductstep.timeout = timeout;
			inductstep.sets_def = sets_def;
			inductstep.sets_any_undef = sets_any_undef;
			inductstep.sets_all_undef = sets_all_undef;
			inductstep.satgen.ignore_div_by_zero = ignore_div_by_zero;
			inductstep.ignore_unknown_cells = ignore_unknown_cells;

			if (!tempinduct_baseonly) {
				inductstep.setup(1);
				inductstep.ez->assume(inductstep.setup_proof(1));
			}

			if (tempinduct_def) {
				std::vector<int> undef_state = inductstep.satgen.importUndefSigSpec(inductstep.satgen.initial_state.export_all(), 1);
				inductstep.ez->assume(inductstep.ez->NOT(inductstep.ez->expression(ezSAT::OpOr, undef_state)));
			}

			for (int inductlen = 1; inductlen <= maxsteps || maxsteps == 0; inductlen++)
			{
				log("\n** Trying induction with length %d **\n", inductlen);

				// phase 1: proving base case

				if (!tempinduct_inductonly)
				{
					basecase.setup(seq_len + inductlen, seq_len + inductlen == 1);
					int property = basecase.setup_proof(seq_len + inductlen);
					basecase.generate_model();

					if (inductlen > 1)
						basecase.force_unique_state(seq_len + 1, seq_len + inductlen);

					if (tempinduct_skip < inductlen)
					{
						log("\n[base case %d] Solving problem with %d variables and %d clauses..\n",
								inductlen, basecase.ez->numCnfVariables(), basecase.ez->numCnfClauses());
						log_flush();

						if (basecase.solve(basecase.ez->NOT(property))) {
							log("SAT temporal induction proof finished - model found for base case: FAIL!\n");
							print_proof_failed();
							basecase.print_model();
							if(!vcd_file_name.empty())
								basecase.dump_model_to_vcd(vcd_file_name);
							if(!json_file_name.empty())
								basecase.dump_model_to_json(json_file_name);
							goto tip_failed;
						}

						if (basecase.gotTimeout)
							goto timeout;

						log("Base case for induction length %d proven.\n", inductlen);
					}
					else
					{
						log("\n[base case %d] Skipping prove for this step (-tempinduct-skip %d).",
								inductlen, tempinduct_skip);
						log("\n[base case %d] Problem size so far: %d variables and %d clauses.\n",
								inductlen, basecase.ez->numCnfVariables(), basecase.ez->numCnfClauses());
					}
					basecase.ez->assume(property);
				}

				// phase 2: proving induction step

				if (!tempinduct_baseonly)
				{
					inductstep.setup(inductlen + 1);
					int property = inductstep.setup_proof(inductlen + 1);
					inductstep.generate_model();

					if (inductlen > 1)
						inductstep.force_unique_state(1, inductlen + 1);

					if (inductlen <= tempinduct_skip || inductlen <= initsteps || inductlen % stepsize != 0)
					{
						if (inductlen < tempinduct_skip)
							log("\n[induction step %d] Skipping prove for this step (-tempinduct-skip %d).",
									inductlen, tempinduct_skip);
						if (inductlen < initsteps)
							log("\n[induction step %d] Skipping prove for this step (-initsteps %d).",
									inductlen, tempinduct_skip);
						if (inductlen % stepsize != 0)
							log("\n[induction step %d] Skipping prove for this step (-stepsize %d).",
									inductlen, stepsize);
						log("\n[induction step %d] Problem size so far: %d variables and %d clauses.\n",
								inductlen, inductstep.ez->numCnfVariables(), inductstep.ez->numCnfClauses());
						inductstep.ez->assume(property);
					}
					else
					{
						if (!cnf_file_name.empty())
						{
							rewrite_filename(cnf_file_name);
							FILE *f = fopen(cnf_file_name.c_str(), "w");
							if (!f)
								log_cmd_error("Can't open output file `%s' for writing: %s\n", cnf_file_name.c_str(), strerror(errno));

							log("Dumping CNF to file `%s'.\n", cnf_file_name.c_str());
							cnf_file_name.clear();

							inductstep.ez->printDIMACS(f, false);
							fclose(f);
						}

						log("\n[induction step %d] Solving problem with %d variables and %d clauses..\n",
								inductlen, inductstep.ez->numCnfVariables(), inductstep.ez->numCnfClauses());
						log_flush();

						if (!inductstep.solve(inductstep.ez->NOT(property))) {
							if (inductstep.gotTimeout)
								goto timeout;
							log("Induction step proven: SUCCESS!\n");
							print_qed();
							goto tip_success;
						}

						log("Induction step failed. Incrementing induction length.\n");
						inductstep.ez->assume(property);
						inductstep.print_model();
					}
				}
			}

			if (tempinduct_baseonly) {
				log("\nReached maximum number of time steps -> proved base case for %d steps: SUCCESS!\n", maxsteps);
				goto tip_success;
			}

			log("\nReached maximum number of time steps -> proof failed.\n");
			if(!vcd_file_name.empty())
				inductstep.dump_model_to_vcd(vcd_file_name);
			if(!json_file_name.empty())
				inductstep.dump_model_to_json(json_file_name);
			print_proof_failed();

		tip_failed:
			if (verify) {
				log("\n");
				log_error("Called with -verify and proof did fail!\n");
			}

			if (0)
		tip_success:
			if (falsify) {
				log("\n");
				log_error("Called with -falsify and proof did succeed!\n");
			}
		}
		else
		{
			if (maxsteps > 0)
				log_cmd_error("The options -maxsteps is only supported for temporal induction proofs!\n");

			SatHelper sathelper(design, module, enable_undef, set_def_formal);

			sathelper.sets = sets;
			sathelper.set_assumes = set_assumes;
			sathelper.prove = prove;
			sathelper.prove_x = prove_x;
			sathelper.prove_asserts = prove_asserts;
			sathelper.sets_at = sets_at;
			sathelper.unsets_at = unsets_at;
			sathelper.shows = shows;
			sathelper.timeout = timeout;
			sathelper.sets_def = sets_def;
			sathelper.sets_any_undef = sets_any_undef;
			sathelper.sets_all_undef = sets_all_undef;
			sathelper.sets_def_at = sets_def_at;
			sathelper.sets_any_undef_at = sets_any_undef_at;
			sathelper.sets_all_undef_at = sets_all_undef_at;
			sathelper.sets_init = sets_init;
			sathelper.set_init_def = set_init_def;
			sathelper.set_init_undef = set_init_undef;
			sathelper.set_init_zero = set_init_zero;
			sathelper.satgen.ignore_div_by_zero = ignore_div_by_zero;
			sathelper.ignore_unknown_cells = ignore_unknown_cells;

			if (seq_len == 0) {
				sathelper.setup();
				if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
					sathelper.ez->assume(sathelper.ez->NOT(sathelper.setup_proof()));
			} else {
				std::vector<int> prove_bits;
				for (int timestep = 1; timestep <= seq_len; timestep++) {
					sathelper.setup(timestep, timestep == 1);
					if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
						if (timestep > prove_skip)
							prove_bits.push_back(sathelper.setup_proof(timestep));
				}
				if (sathelper.prove.size() || sathelper.prove_x.size() || sathelper.prove_asserts)
					sathelper.ez->assume(sathelper.ez->NOT(sathelper.ez->expression(ezSAT::OpAnd, prove_bits)));
			}
			sathelper.generate_model();

			if (!cnf_file_name.empty())
			{
				rewrite_filename(cnf_file_name);
				FILE *f = fopen(cnf_file_name.c_str(), "w");
				if (!f)
					log_cmd_error("Can't open output file `%s' for writing: %s\n", cnf_file_name.c_str(), strerror(errno));

				log("Dumping CNF to file `%s'.\n", cnf_file_name.c_str());
				cnf_file_name.clear();

				sathelper.ez->printDIMACS(f, false);
				fclose(f);
			}

			int rerun_counter = 0;

		rerun_solver:
			log("\nSolving problem with %d variables and %d clauses..\n",
					sathelper.ez->numCnfVariables(), sathelper.ez->numCnfClauses());
			log_flush();

			if (sathelper.solve())
			{
				if (max_undef) {
					log("SAT model found. maximizing number of undefs.\n");
					sathelper.maximize_undefs();
				}

				if (!prove.size() && !prove_x.size() && !prove_asserts) {
					log("SAT solving finished - model found:\n");
				} else {
					log("SAT proof finished - model found: FAIL!\n");
					print_proof_failed();
				}

				sathelper.print_model();

				if(!vcd_file_name.empty())
					sathelper.dump_model_to_vcd(vcd_file_name);
				if(!json_file_name.empty())
					sathelper.dump_model_to_json(json_file_name);

				if (loopcount != 0) {
					loopcount--, rerun_counter++;
					sathelper.invalidate_model(max_undef);
					goto rerun_solver;
				}

				if (!prove.size() && !prove_x.size() && !prove_asserts) {
					if (falsify) {
						log("\n");
						log_error("Called with -falsify and found a model!\n");
					}
				} else {
					if (verify) {
						log("\n");
						log_error("Called with -verify and proof did fail!\n");
					}
				}
			}
			else
			{
				if (sathelper.gotTimeout)
					goto timeout;
				if (rerun_counter)
					log("SAT solving finished - no more models found (after %d distinct solutions).\n", rerun_counter);
				else if (!prove.size() && !prove_x.size() && !prove_asserts) {
					log("SAT solving finished - no model found.\n");
					if (verify) {
						log("\n");
						log_error("Called with -verify and found no model!\n");
					}
				} else {
					log("SAT proof finished - no model found: SUCCESS!\n");
					print_qed();
					if (falsify) {
						log("\n");
						log_error("Called with -falsify and proof did succeed!\n");
					}
				}
			}

			if (!prove.size() && !prove_x.size() && !prove_asserts) {
				if (falsify && rerun_counter) {
					log("\n");
					log_error("Called with -falsify and found a model!\n");
				}
			} else {
				if (verify && rerun_counter) {
					log("\n");
					log_error("Called with -verify and proof did fail!\n");
				}
			}
		}

		if (0) {
	timeout:
			log("Interrupted SAT solver: TIMEOUT!\n");
			print_timeout();
			if (fail_on_timeout)
				log_error("Called with -verify and proof did time out!\n");
		}
	}
} SatPass;

PRIVATE_NAMESPACE_END
