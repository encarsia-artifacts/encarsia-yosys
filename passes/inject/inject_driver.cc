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
	Pass::call(design, "write_rtlil " + host_directory + "/host_driver.rtlil");
}

static void write_reference(RTLIL::Design *design, std::string output_directory, int index){
	std::string host_directory = output_directory + "/" + std::to_string(index);
	Pass::call(design, "write_rtlil " + host_directory + "/reference_driver.rtlil");
}

static void expose_cells(RTLIL::Module *module){
	for (auto cell : module->selected_cells()) {
		if (cell->type == ID($memrd)) continue;
		if (cell->type == ID($memrd_v2)) continue;
		if (cell->type == ID($memwr)) continue;
		if (cell->type == ID($memwr_v2)) continue;
		if (cell->type == ID($meminit)) continue;
		if (cell->type == ID($meminit_v2)) continue;
		if (cell->type == ID($mem)) continue;
		if (cell->type == ID($mem_v2)) continue;

		if (cell->type == ID($ff)) continue;
		if (cell->type == ID($dff)) continue;
		if (cell->type == ID($dffe)) continue;
		if (cell->type == ID($dffse)) continue;
		if (cell->type == ID($dffsre)) continue;
		if (cell->type == ID($adff)) continue;
		if (cell->type == ID($sdff)) continue;
		if (cell->type == ID($sdffe)) continue;
		if (cell->type == ID($sdffce)) continue;
		if (cell->type == ID($adffe)) continue;
		if (cell->type == ID($aldff)) continue;
		if (cell->type == ID($aldffe)) continue;
		if (cell->type == ID($dlatch)) continue;
		if (cell->type == ID($adlatch)) continue;
		if (cell->type == ID($dlatchsr)) continue;
		if (cell->type == ID($fsm)) continue;
		for (auto connection : cell->connections()) {
			RTLIL::IdString port = connection.first;
			RTLIL::SigSpec signal = connection.second;

			RTLIL::Wire *intermediate_wire = module->addWire(NEW_ID, signal.size());
			// TODO possibly unnecessary
			cell->unsetPort(port);
			cell->setPort(port, RTLIL::SigSpec(intermediate_wire));
			if (cell->input(port)) {
				module->connect(RTLIL::SigSpec(intermediate_wire), signal);
			} else {
				module->connect(signal, RTLIL::SigSpec(intermediate_wire));
			}
		}
	}
}

struct InjectDriverPass : public Pass {
	InjectDriverPass() : Pass("inject_driver", "produce designs with signal mix-ups.") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    inject_driver [options] [selection]\n");
		log("\n");
		log("This pass produces designs with signal mix-ups.\n");
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

		log_header(design, "Inject Driver.\n");

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

		for (auto module : design->selected_modules()) {
			std::set<RTLIL::SigSpec> drivers_set, targets_set;

			expose_cells(module);
			// SigMap sigmap(module);
			// std::vector<RTLIL::Wire *> public_wires;
			// for (auto wire : module->selected_wires()) {
			// 	if (wire->name.isPublic()) public_wires.push_back(wire);
			// }

			for (auto connection : module->connections()) {
				RTLIL::SigSpec driver = connection.second;
				RTLIL::SigSpec target = connection.first;
				std::set<RTLIL::SigSpec> current_drivers, current_targets;
				if (!target.is_wire()) continue;
				if (driver.size() == 0) continue;

				int offset = 0;
				for (auto chunk : driver.chunks()) {
					RTLIL::SigSpec chunk_signal(chunk);
					if (!chunk.is_wire() || (chunk.is_wire() && chunk.wire->name.isPublic())){
						current_drivers.insert(chunk_signal);
						current_targets.insert(target.extract(offset, chunk_signal.size()));
						offset += chunk_signal.size();
						continue;
					}

					// sigmap.apply(chunk_signal);
					// for (auto public_wire : public_wires) {
					// 	RTLIL::SigSpec temp = chunk_signal;

					// 	temp.replace(sigmap(public_wire), RTLIL::SigSpec(public_wire));
					// 	if (temp.is_chunk() && temp.as_chunk().is_wire() && temp.as_chunk().wire->name.isPublic()) {
					// 		current_drivers.insert(temp);
					// 		current_targets.insert(target.extract(offset, chunk_signal.size()));
					// 		offset += chunk_signal.size();
					// 		break;
					// 	}
					// }
				}

				if (offset != driver.size()) continue;
				drivers_set.insert(current_drivers.begin(), current_drivers.end());
				targets_set.insert(current_targets.begin(), current_targets.end());
			}

			std::vector<RTLIL::SigSpec> drivers(drivers_set.begin(), drivers_set.end()), targets(targets_set.begin(), targets_set.end());
			int start_index = index;
			while (index-start_index < bugs_per_module) {
				RTLIL::SigSpec driver = drivers.at(rand() % (int)drivers.size());
				RTLIL::SigSpec target = targets.at(rand() % (int)targets.size());

				if (!driver.extract(target).empty()) continue;

				if (driver.size() < target.size()) {
					if (driver.is_fully_const()) {
						driver.append(RTLIL::Const(driver.as_const().bits.back(), target.size()-driver.size()));
					} else {
						target = target.extract(0, driver.size());
					}
				} else if (driver.size() > target.size()) {
					driver = driver.extract(0, target.size());
				}

				if (!target.is_wire()) continue;
				
				for (auto &connection : module->connections_) {
					if (connection.first.extract(target).empty()) continue;
					// log("driver: %s\n", log_signal(driver));
					// log("target: %s\n", log_signal(target));
					// log("extract: %s\n", log_signal(connection.first.extract(target)));
					// log("connection.first: %s\n", log_signal(connection.first));
					// log("connection.second: %s\n", log_signal(connection.second));
					++index;

					RTLIL::SigSpec original_driver = connection.second;
					// log("before: %s %s\n", log_signal(connection.first), log_signal(connection.second));
					connection.first.replace(target, driver, &connection.second);
					if (connection.second == original_driver) break;
					target.as_wire()->attributes[ID(buggy)] = RTLIL::Const("buggy");
					// log("after: %s %s\n", log_signal(connection.first), log_signal(connection.second));
					write_design(design, output_directory, index);
					target.as_wire()->attributes.erase(ID(buggy));
					connection.second = original_driver;
					write_reference(design, output_directory, index);
					// log("back again: %s %s\n\n", log_signal(connection.first), log_signal(connection.second));
					break;
				}
			}
		}
	}
} InjectDriverPass;

PRIVATE_NAMESPACE_END