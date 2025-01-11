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
	Pass::call(design, "opt -full -fine");
	Pass::call(design, "write_rtlil miter.rtlil");
	Pass::call(design, "write_verilog -noattr miter.v");
}

// TODO take care of inconsistent naming cell/amt
static RTLIL::Module *create_miter(RTLIL::Design *design, RTLIL::Module *host_module, RTLIL::Wire *host_target, RTLIL::Module *reference_module, RTLIL::Wire *reference_target, std::vector<std::string> &observables)
{
	SigMap host_sigmap(host_module);
	RTLIL::SigSpec host_output(host_target);
	RTLIL::SigSpec host_observables;


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
	RTLIL::SigSpec reference_output(reference_target);
	RTLIL::SigSpec reference_observables;


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

		if (host_wire->name.str() == "\\output" || host_wire->name.str() == "\\observables")
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

struct CreateMiterPass : public Pass {
	CreateMiterPass() : Pass("create_miter", "create miter for bug verification") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::vector<std::string> observables;

		log_header(design, "Executing CreateMiterPass pass.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-observable" && argidx+1 < args.size()) {
				observables.push_back(args[++argidx]);
				continue;
			}
		}
		if (observables.empty()) {
			log_error("Missing mandatory argument -observable!\n");
		}

        RTLIL::Module *host_module = design->module("\\host");
        if (!host_module) {
            log_error("Can not find host module in current design!\n");
        }
        RTLIL::Module *reference_module = design->module("\\reference");
        if (!reference_module) {
            log_error("Can not find reference module in current design!\n");
        }

        RTLIL::Wire *host_wire = nullptr;
        RTLIL::Wire *reference_wire = nullptr;
        for (auto wire : host_module->selected_wires()) {
            if (!wire->attributes.count(ID(buggy))) continue;

            host_wire = wire;
            reference_wire = reference_module->wire(wire->name);
            if (!reference_wire) {
                log_error("Can not find buggy wire in reference module!\n");
            }

            // TODO eventually implement multiple buggy cells
            break;
        }
		if (!host_wire) {
			log_error("Can not find buggy wire in host module!\n");
		}

        RTLIL::Module *miter_module = create_miter(design, host_module, host_wire, reference_module, reference_wire, observables);
		synthetize_miter(design, miter_module->name.str());
	}
} CreateMiterPass;

PRIVATE_NAMESPACE_END