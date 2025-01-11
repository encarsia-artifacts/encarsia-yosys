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

// TODO only include selection once!!!
#ifndef SELECTION_H
#define SELECTION_H

#include "kernel/yosys.h"

YOSYS_NAMESPACE_BEGIN

struct selection_t {RTLIL::Const select; RTLIL::SigSpec output; bool buggy;};

static void copy_to_cell(RTLIL::Cell *cell, std::vector<selection_t> &selections){
	RTLIL::SigSpec new_input;

	cell->parameters[ID::STATE_TABLE] = RTLIL::Const();
	std::vector<RTLIL::State> &bits_table = cell->parameters[ID::STATE_TABLE].bits;
	for (int i = 0; i < int(selections.size()); i++) {
		std::vector<RTLIL::State> &bits_state = selections[i].select.bits;
		bits_table.insert(bits_table.end(), bits_state.begin(), bits_state.end());
		bits_table.insert(bits_table.end(), selections.at(i).buggy ? RTLIL::S1 : RTLIL::S0);
		new_input.append(selections.at(i).output);
	}

	cell->unsetPort(ID::A);
	cell->setPort(ID::A, new_input);
}

static void copy_from_cell(RTLIL::Cell *cell, std::vector<selection_t> &selections){
	int selection_size = GetSize(cell->getPort(ID::S));
	int output_size = GetSize(cell->getPort(ID::Y));
	std::vector<RTLIL::State> &bits_table = cell->parameters[ID::STATE_TABLE].bits;
	for (size_t i = 0; i < bits_table.size()/(selection_size+1); ++i) {
		RTLIL::Const selection;
		int off_begin = i*(selection_size+1), off_end = off_begin + selection_size;
		selection.bits.insert(selection.bits.begin(), bits_table.begin()+off_begin, bits_table.begin()+off_end);
		selections.push_back({selection, cell->getPort(ID::A).extract(i*output_size, output_size), bits_table.at(off_end) == RTLIL::S1 ? true : false});
	}
}

static void log_amt(RTLIL::Cell *cell, std::vector<selection_t> &selections) {
	log("AMT cell: %s\n", cell->name.c_str());
	log("Output: %s\n", log_signal(cell->getPort(ID::Y)));
	log("Select: %s\n", log_signal(cell->getPort(ID::S)));

	for (int i = 0; i < GetSize(selections); i++) {
		log("  %5d: %s = %s %s\n", i, log_signal(selections.at(i).select), log_signal(selections.at(i).output), log_signal(selections.at(i).buggy));
	}
	log("\n");
}

static void log_bug(RTLIL::Cell *cell, std::vector<selection_t> &selections, std::vector<selection_t> &buggy_selections) {
	log("Injecting bug:\n");
	log("Output: %s\n", log_signal(cell->getPort(ID::Y)));
	log("Select: %s\n", log_signal(cell->getPort(ID::S)));

	for (int i = 0; i < GetSize(selections); i++) {
		if (selections.at(i).output == buggy_selections.at(i).output) log("  %5d: %s = %s\n", i, log_signal(selections.at(i).select), log_signal(selections.at(i).output));
		else log("  %5d: %s = %s -> %s\n", i, log_signal(selections.at(i).select), log_signal(selections.at(i).output), log_signal(buggy_selections.at(i).output));
	}
	log("\n");
}

YOSYS_NAMESPACE_END

#endif