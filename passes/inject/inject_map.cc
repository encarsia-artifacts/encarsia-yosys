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

static void map_amt(RTLIL::Cell *amt_cell, RTLIL::Module *module)
{
	log("Mapping AMT %s from module %s.\n", amt_cell->name.c_str(), module->name.c_str());

	std::vector<selection_t> selections;
	copy_from_cell(amt_cell, selections);

	static SigMap assign_map(module);
	RTLIL::SigSpec amt_s = assign_map(amt_cell->getPort(ID::S));
	RTLIL::SigSpec sig_y = assign_map(amt_cell->getPort(ID::Y));
	// TODO replace with a more principled default value
	RTLIL::SigSpec sig_a = RTLIL::Const(0, sig_y.size());
	RTLIL::SigSpec sig_b = assign_map(amt_cell->getPort(ID::A));
	RTLIL::SigSpec sig_s = RTLIL::SigSpec(module->addWire(NEW_ID, selections.size()));

	for (int i = 0; i < GetSize(selections); ++i) {
		selection_t selection = selections.at(i);
		RTLIL::SigSpec eq_sig_a, eq_sig_b;

		for (size_t j = 0; j < selection.select.bits.size(); j++){
			if(selection.select.bits.at(j) == RTLIL::State::S0 || selection.select.bits.at(j) == RTLIL::State::S1){
				eq_sig_a.append(amt_s.extract(j, 1));
				eq_sig_b.append(RTLIL::SigSpec(selection.select.bits.at(j)));
			}
		}

		RTLIL::Cell *eq_cell = module->addCell(NEW_ID, ID($eq));
		eq_cell->setPort(ID::A, eq_sig_a);
		eq_cell->setPort(ID::B, eq_sig_b);
		eq_cell->setPort(ID::Y, sig_s.extract(i));
		eq_cell->parameters[ID::A_SIGNED] = RTLIL::Const(false);
		eq_cell->parameters[ID::B_SIGNED] = RTLIL::Const(false);
		eq_cell->parameters[ID::A_WIDTH] = RTLIL::Const(eq_sig_a.size());
		eq_cell->parameters[ID::B_WIDTH] = RTLIL::Const(eq_sig_b.size());
		eq_cell->parameters[ID::Y_WIDTH] = RTLIL::Const(1);
	}

	//

	module->addPmux(NEW_ID, sig_a, sig_b, sig_s, sig_y);

	// Remove AMT cell

	module->remove(amt_cell);
}

struct InjectMapPass : public Pass {
	InjectMapPass() : Pass("inject_map", "map AMTs to basic logic") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    inject_map [selection]\n");
		log("\n");
		log("This pass maps AMT cells to basic logic.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing INJECT_MAP pass (mapping AMTs to basic logic).\n");
		extra_args(args, 1, design);

		for (auto mod : design->selected_modules()) {
			std::vector<RTLIL::Cell*> amt_cells;
			for (auto cell : mod->selected_cells())
				if (cell->type == ID($amt))
					amt_cells.push_back(cell);
			for (auto cell : amt_cells)
					map_amt(cell, mod);
		}
	}
} InjectMapPass;

PRIVATE_NAMESPACE_END
