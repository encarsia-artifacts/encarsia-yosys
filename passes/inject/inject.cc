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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct InjectPass : public Pass {
	InjectPass() : Pass("inject", "inject bugs into the design") { }
	// TODO better log
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("  inject [options] [selection]\n");
		log("\n");
		log("This pass injects architectural bugs into the design.\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string output_directory;

		// TODO better log
		log_header(design, "Injecting Bugs!!!\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-output-dir" && argidx+1 < args.size() && output_directory.empty()) {
				output_directory = args[++argidx];
				continue;
			}
		}
		if (output_directory.empty()) {
			log_error("Missing mandatory argument -output-dir!\n");
		}

		Pass::call(design, "inject_detect");
		Pass::call(design, "inject_extract");
		Pass::call(design, "write_rtlil " + output_directory + "/reference.rtlil");
		Pass::call(design, "inject_amt -output-dir " + output_directory);
	}
} InjectPass;

PRIVATE_NAMESPACE_END
