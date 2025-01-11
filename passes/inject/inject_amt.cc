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

// TODO check whether these are actually needed
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
#include <sys/stat.h>
#include "selection.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static void write_design(RTLIL::Design *design, std::string output_directory, int index){
	std::string host_directory = output_directory + "/" + std::to_string(index);
	if (mkdir(host_directory.c_str(), 0755)){
		log_error("Error creating bug directory: %s.\n", strerror(errno));
	}
	// TODO remove this call maybe
	Pass::call(design, "write_rtlil " + host_directory + "/host_amt.rtlil");
}

struct InjectAmtPass : public Pass {
	InjectAmtPass() : Pass("inject_amt", "produce designs with buggy AMTs") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    inject_amt [options] [selection]\n");
		log("\n");
		log("This pass produces designs with buggy AMTs.\n");
		log("\n");
		log("Options:\n");
		log("\n");
		log("    -output-dir directory\n");
		log("        generated designs are stored in the directory\n");
		log("    -num-bugs number\n");
		log("        the desired number of bugs to be injected into the design\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string output_directory;
		int num_bugs = 1000;
		int bugs_per_module;
		int index = 0;

		log_header(design, "Executing InjectAmt pass (producing designs with buggy AMTs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-output-dir" && argidx+1 < args.size() && output_directory.empty()) {
				output_directory = args[++argidx];
				continue;
			}
			if (args[argidx] == "-num-bugs" && argidx+1 < args.size()) {
				num_bugs = atoi(args[++argidx].c_str());
				continue;
			}
		}
		if (output_directory.empty()) {
			log_error("Missing mandatory argument -output-dir!\n");
		}

		bugs_per_module = num_bugs / design->selected_modules().size();
		if (!bugs_per_module) bugs_per_module = 1;

		// TODO create hosts directory

		for (auto module : design->selected_modules()) {
			int num_amt_cells = 0;
			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($amt)) {
					std::vector<selection_t> selections;
					copy_from_cell(cell, selections);
					if (selections.size() < 4) continue;
					++num_amt_cells;
				}
			}
			if (!num_amt_cells) continue;
			int bugs_per_cell = bugs_per_module / num_amt_cells;
			if (!bugs_per_cell) bugs_per_cell = 1;

			for (auto cell : module->selected_cells()) {
				if (cell->type == ID($amt)) {
					std::vector<selection_t> selections;
					copy_from_cell(cell, selections);
					if (selections.size() < 4) continue;
					log_amt(cell, selections);

					std::vector<std::vector<selection_t>> bugs;
					int selection_index = -1;
					for (auto &selection : selections) {
						++selection_index;
						if (selection.output.is_fully_undef()) continue;
						for (auto &bit : selection.select.bits) {
							int one_in = selections.size() * selection.select.size() / bugs_per_cell;
							if (!one_in) one_in = 1;
							// if ((rand() % 0xffffffffffff) == 0) {
							if ((rand() % one_in) == 0) {
								if (bit == RTLIL::State::S0 || bit == RTLIL::State::S1) {
									RTLIL::State temp = bit;
									bit = RTLIL::State::Sa;
									selection.buggy = true;
									bugs.push_back(selections);
									bugs.back().erase(bugs.back().begin() + selection_index);
									bugs.back().insert(bugs.back().begin(), selection);
									selection.buggy = false;
									bit = temp;
								} else if (bit == RTLIL::State::Sa) {
									bit = (rand() & 1) ? RTLIL::State::S1 : RTLIL::State::S0;
									selection.buggy = true;
									bugs.push_back(selections);
									selection.buggy = false;
									bit = RTLIL::State::Sa;
								}
							}
						}
					}

					for (int i = 0; i < 1; ++i) {
						std::vector<selection_t> buggy_selections = selections;
						buggy_selections.erase(buggy_selections.begin()+(rand()%(selections.size() + 1)));
						bugs.push_back(buggy_selections);
					}

					cell->attributes[ID(buggy)] = RTLIL::Const("buggy");
					cell->getPort(ID::Y).as_wire()->attributes[ID(buggy)] = RTLIL::Const("buggy");
					for (auto &bug : bugs) {
						copy_to_cell(cell, bug);
						write_design(design, output_directory, ++index);
					}
					copy_to_cell(cell, selections);
					cell->attributes.erase(ID(buggy));
					cell->getPort(ID::Y).as_wire()->attributes.erase(ID(buggy));
				}
			}
		}
	}
} InjectAmtPass;

PRIVATE_NAMESPACE_END