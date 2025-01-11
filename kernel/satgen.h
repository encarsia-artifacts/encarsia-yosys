/* -*- c++ -*-
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

#ifndef SATGEN_H
#define SATGEN_H

#include "kernel/rtlil.h"
#include "kernel/sigtools.h"
#include "kernel/celltypes.h"
#include "kernel/macc.h"

#include "libs/ezsat/ezminisat.h"

YOSYS_NAMESPACE_BEGIN

// defined in kernel/register.cc
extern struct SatSolver *yosys_satsolver_list;
extern struct SatSolver *yosys_satsolver;

struct SatSolver
{
	string name;
	SatSolver *next;
	virtual ezSAT *create() = 0;

	SatSolver(string name) : name(name) {
		next = yosys_satsolver_list;
		yosys_satsolver_list = this;
	}

	virtual ~SatSolver() {
		auto p = &yosys_satsolver_list;
		while (*p) {
			if (*p == this)
				*p = next;
			else
				p = &(*p)->next;
		}
		if (yosys_satsolver == this)
			yosys_satsolver = yosys_satsolver_list;
	}
};

struct ezSatPtr : public std::unique_ptr<ezSAT> {
	ezSatPtr() : unique_ptr<ezSAT>(yosys_satsolver->create()) { }
};

struct SatGen
{
	ezSAT *ez;
	SigMap *sigmap;
	std::string prefix;
	SigPool initial_state;
	std::map<std::string, RTLIL::SigSpec> asserts_a, asserts_en;
	std::map<std::string, RTLIL::SigSpec> assumes_a, assumes_en;
	std::map<std::string, std::map<RTLIL::SigBit, int>> imported_signals;
	std::map<std::pair<std::string, int>, bool> initstates;
	bool ignore_div_by_zero;
	bool model_undef;
	bool def_formal = false;

	SatGen(ezSAT *ez, SigMap *sigmap, std::string prefix = std::string()) :
			ez(ez), sigmap(sigmap), prefix(prefix), ignore_div_by_zero(false), model_undef(false)
	{
	}

	void setContext(SigMap *sigmap, std::string prefix = std::string())
	{
		this->sigmap = sigmap;
		this->prefix = prefix;
	}

	std::vector<int> importSigSpecWorker(RTLIL::SigSpec sig, std::string &pf, bool undef_mode, bool dup_undef)
	{
		log_assert(!undef_mode || model_undef);
		sigmap->apply(sig);

		std::vector<int> vec;
		vec.reserve(GetSize(sig));

		for (auto &bit : sig)
			if (bit.wire == NULL) {
				if (model_undef && dup_undef && bit == RTLIL::State::Sx)
					vec.push_back(ez->frozen_literal());
				else
					vec.push_back(bit == (undef_mode ? RTLIL::State::Sx : RTLIL::State::S1) ? ez->CONST_TRUE : ez->CONST_FALSE);
			} else {
				std::string name = pf + (bit.wire->width == 1 ? stringf("%s", log_id(bit.wire)) : stringf("%s [%d]", log_id(bit.wire->name), bit.offset));
				vec.push_back(ez->frozen_literal(name));
				imported_signals[pf][bit] = vec.back();
			}
		return vec;
	}

	std::vector<int> importSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, false, false);
	}

	std::vector<int> importDefSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, false, true);
	}

	std::vector<int> importUndefSigSpec(RTLIL::SigSpec sig, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = "undef:" + prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(sig, pf, true, false);
	}

	int importSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, false, false).front();
	}

	int importDefSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, false, true).front();
	}

	int importUndefSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = "undef:" + prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return importSigSpecWorker(bit, pf, true, false).front();
	}

	bool importedSigBit(RTLIL::SigBit bit, int timestep = -1)
	{
		log_assert(timestep != 0);
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		return imported_signals[pf].count(bit) != 0;
	}

	void getAsserts(RTLIL::SigSpec &sig_a, RTLIL::SigSpec &sig_en, int timestep = -1)
	{
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		sig_a = asserts_a[pf];
		sig_en = asserts_en[pf];
	}

	void getAssumes(RTLIL::SigSpec &sig_a, RTLIL::SigSpec &sig_en, int timestep = -1)
	{
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		sig_a = assumes_a[pf];
		sig_en = assumes_en[pf];
	}

	int importAsserts(int timestep = -1)
	{
		std::vector<int> check_bits, enable_bits;
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		if (model_undef) {
			check_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(asserts_a[pf], timestep)), importDefSigSpec(asserts_a[pf], timestep));
			enable_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(asserts_en[pf], timestep)), importDefSigSpec(asserts_en[pf], timestep));
		} else {
			check_bits = importDefSigSpec(asserts_a[pf], timestep);
			enable_bits = importDefSigSpec(asserts_en[pf], timestep);
		}
		return ez->vec_reduce_and(ez->vec_or(check_bits, ez->vec_not(enable_bits)));
	}

	int importAssumes(int timestep = -1)
	{
		std::vector<int> check_bits, enable_bits;
		std::string pf = prefix + (timestep == -1 ? "" : stringf("@%d:", timestep));
		if (model_undef) {
			check_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(assumes_a[pf], timestep)), importDefSigSpec(assumes_a[pf], timestep));
			enable_bits = ez->vec_and(ez->vec_not(importUndefSigSpec(assumes_en[pf], timestep)), importDefSigSpec(assumes_en[pf], timestep));
		} else {
			check_bits = importDefSigSpec(assumes_a[pf], timestep);
			enable_bits = importDefSigSpec(assumes_en[pf], timestep);
		}
		return ez->vec_reduce_and(ez->vec_or(check_bits, ez->vec_not(enable_bits)));
	}

	int signals_eq(RTLIL::SigSpec lhs, RTLIL::SigSpec rhs, int timestep_lhs = -1, int timestep_rhs = -1)
	{
		if (timestep_rhs < 0)
			timestep_rhs = timestep_lhs;

		log_assert(lhs.size() == rhs.size());

		std::vector<int> vec_lhs = importSigSpec(lhs, timestep_lhs);
		std::vector<int> vec_rhs = importSigSpec(rhs, timestep_rhs);

		if (!model_undef)
			return ez->vec_eq(vec_lhs, vec_rhs);

		std::vector<int> undef_lhs = importUndefSigSpec(lhs, timestep_lhs);
		std::vector<int> undef_rhs = importUndefSigSpec(rhs, timestep_rhs);

		std::vector<int> eq_bits;
		for (int i = 0; i < lhs.size(); i++)
			eq_bits.push_back(ez->AND(ez->IFF(undef_lhs.at(i), undef_rhs.at(i)),
					ez->IFF(ez->OR(vec_lhs.at(i), undef_lhs.at(i)), ez->OR(vec_rhs.at(i), undef_rhs.at(i)))));
		return ez->expression(ezSAT::OpAnd, eq_bits);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, RTLIL::Cell *cell, size_t y_width = 0, bool forced_signed = false)
	{
		bool is_signed = forced_signed;
		if (!forced_signed && cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters.count(ID::B_SIGNED) > 0)
			is_signed = cell->parameters[ID::A_SIGNED].as_bool() && cell->parameters[ID::B_SIGNED].as_bool();
		while (vec_a.size() < vec_b.size() || vec_a.size() < y_width)
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->CONST_FALSE);
		while (vec_b.size() < vec_a.size() || vec_b.size() < y_width)
			vec_b.push_back(is_signed && vec_b.size() > 0 ? vec_b.back() : ez->CONST_FALSE);
	}

	void extendSignalWidth(std::vector<int> &vec_a, std::vector<int> &vec_b, std::vector<int> &vec_y, RTLIL::Cell *cell, bool forced_signed = false)
	{
		extendSignalWidth(vec_a, vec_b, cell, vec_y.size(), forced_signed);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	void extendSignalWidthUnary(std::vector<int> &vec_a, std::vector<int> &vec_y, RTLIL::Cell *cell, bool forced_signed = false)
	{
		bool is_signed = forced_signed || (cell->parameters.count(ID::A_SIGNED) > 0 && cell->parameters[ID::A_SIGNED].as_bool());
		while (vec_a.size() < vec_y.size())
			vec_a.push_back(is_signed && vec_a.size() > 0 ? vec_a.back() : ez->CONST_FALSE);
		while (vec_y.size() < vec_a.size())
			vec_y.push_back(ez->literal());
	}

	void undefGating(std::vector<int> &vec_y, std::vector<int> &vec_yy, std::vector<int> &vec_undef)
	{
		log_assert(model_undef);
		log_assert(vec_y.size() == vec_yy.size());
		if (vec_y.size() > vec_undef.size()) {
			std::vector<int> trunc_y(vec_y.begin(), vec_y.begin() + vec_undef.size());
			std::vector<int> trunc_yy(vec_yy.begin(), vec_yy.begin() + vec_undef.size());
			ez->assume(ez->expression(ezSAT::OpAnd, ez->vec_or(vec_undef, ez->vec_iff(trunc_y, trunc_yy))));
		} else {
			log_assert(vec_y.size() == vec_undef.size());
			ez->assume(ez->expression(ezSAT::OpAnd, ez->vec_or(vec_undef, ez->vec_iff(vec_y, vec_yy))));
		}
	}

	std::pair<std::vector<int>, std::vector<int>> mux(int s, int undef_s, const std::vector<int> &a, const std::vector<int> &undef_a, const std::vector<int> &b, const std::vector<int> &undef_b) {
		std::vector<int> res;
		std::vector<int> undef_res;
		res = ez->vec_ite(s, b, a);
		if (model_undef) {
			std::vector<int> unequal_ab = ez->vec_not(ez->vec_iff(a, b));
			std::vector<int> undef_ab = ez->vec_or(unequal_ab, ez->vec_or(undef_a, undef_b));
			undef_res = ez->vec_ite(undef_s, undef_ab, ez->vec_ite(s, undef_b, undef_a));
		}
		return std::make_pair(res, undef_res);
	}

	void undefGating(int y, int yy, int undef)
	{
		ez->assume(ez->OR(undef, ez->IFF(y, yy)));
	}

	void setInitState(int timestep)
	{
		auto key = make_pair(prefix, timestep);
		log_assert(initstates.count(key) == 0 || initstates.at(key) == true);
		initstates[key] = true;
	}

	bool importCell(RTLIL::Cell *cell, int timestep = -1);
};

struct SatHelper
{
	RTLIL::Design *design;
	RTLIL::Module *module;

	SigMap sigmap;
	CellTypes ct;

	ezSatPtr ez;
	SatGen satgen;

	// additional constraints
	std::vector<std::pair<std::string, std::string>> sets, prove, prove_x, sets_init;
	std::map<int, std::vector<std::pair<std::string, std::string>>> sets_at;
	std::map<int, std::vector<std::string>> unsets_at;
	bool prove_asserts, set_assumes;

	// undef constraints
	bool enable_undef, set_init_def, set_init_undef, set_init_zero, ignore_unknown_cells;
	std::vector<std::string> sets_def, sets_any_undef, sets_all_undef;
	std::map<int, std::vector<std::string>> sets_def_at, sets_any_undef_at, sets_all_undef_at;

	// model variables
	std::vector<std::string> shows;
	SigPool show_signal_pool;
	SigSet<RTLIL::Cell*> show_drivers;
	int max_timestep, timeout;
	bool gotTimeout;

	SatHelper(RTLIL::Design *design, RTLIL::Module *module, bool enable_undef, bool set_def_formal) :
		design(design), module(module), sigmap(module), ct(design), satgen(ez.get(), &sigmap)
	{
		this->enable_undef = enable_undef;
		satgen.model_undef = enable_undef;
		satgen.def_formal = set_def_formal;
		set_init_def = false;
		set_init_undef = false;
		set_init_zero = false;
		ignore_unknown_cells = false;
		max_timestep = -1;
		timeout = 0;
		gotTimeout = false;
	}

	void check_undef_enabled(const RTLIL::SigSpec &sig)
	{
		if (enable_undef)
			return;

		std::vector<RTLIL::SigBit> sigbits = sig.to_sigbit_vector();
		for (size_t i = 0; i < sigbits.size(); i++)
			if (sigbits[i].wire == NULL && sigbits[i].data == RTLIL::State::Sx)
				log_cmd_error("Bit %d of %s is undef but option -enable_undef is missing!\n", int(i), log_signal(sig));
	}

	void setup(int timestep = -1, bool initstate = false)
	{
		if (timestep > 0)
			log ("\nSetting up time step %d:\n", timestep);
		else
			log ("\nSetting up SAT problem:\n");

		if (initstate)
			satgen.setInitState(timestep);

		if (timestep > max_timestep)
			max_timestep = timestep;

		RTLIL::SigSpec big_lhs, big_rhs;

		for (auto &s : sets)
		{
			RTLIL::SigSpec lhs, rhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.size() != rhs.size())
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

			log("Import set-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : sets_at[timestep])
		{
			RTLIL::SigSpec lhs, rhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
			if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
				log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
			show_signal_pool.add(sigmap(lhs));
			show_signal_pool.add(sigmap(rhs));

			if (lhs.size() != rhs.size())
				log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
					s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

			log("Import set-constraint for this timestep: %s = %s\n", log_signal(lhs), log_signal(rhs));
			big_lhs.remove2(lhs, &big_rhs);
			big_lhs.append(lhs);
			big_rhs.append(rhs);
		}

		for (auto &s : unsets_at[timestep])
		{
			RTLIL::SigSpec lhs;

			if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s))
				log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.c_str());
			show_signal_pool.add(sigmap(lhs));

			log("Import unset-constraint for this timestep: %s\n", log_signal(lhs));
			big_lhs.remove2(lhs, &big_rhs);
		}

		log("Final constraint equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
		check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
		ez->assume(satgen.signals_eq(big_lhs, big_rhs, timestep));

		// 0 = sets_def
		// 1 = sets_any_undef
		// 2 = sets_all_undef
		std::set<RTLIL::SigSpec> sets_def_undef[3];

		for (auto &s : sets_def) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].insert(sig);
		}

		for (auto &s : sets_any_undef) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[1].insert(sig);
		}

		for (auto &s : sets_all_undef) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[2].insert(sig);
		}

		for (auto &s : sets_def_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].insert(sig);
			sets_def_undef[1].erase(sig);
			sets_def_undef[2].erase(sig);
		}

		for (auto &s : sets_any_undef_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].erase(sig);
			sets_def_undef[1].insert(sig);
			sets_def_undef[2].erase(sig);
		}

		for (auto &s : sets_all_undef_at[timestep]) {
			RTLIL::SigSpec sig;
			if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
				log_cmd_error("Failed to parse set-def expression `%s'.\n", s.c_str());
			sets_def_undef[0].erase(sig);
			sets_def_undef[1].erase(sig);
			sets_def_undef[2].insert(sig);
		}

		for (int t = 0; t < 3; t++)
		for (auto &sig : sets_def_undef[t]) {
			log("Import %s constraint for this timestep: %s\n", t == 0 ? "def" : t == 1 ? "any_undef" : "all_undef", log_signal(sig));
			std::vector<int> undef_sig = satgen.importUndefSigSpec(sig, timestep);
			if (t == 0)
				ez->assume(ez->NOT(ez->expression(ezSAT::OpOr, undef_sig)));
			if (t == 1)
				ez->assume(ez->expression(ezSAT::OpOr, undef_sig));
			if (t == 2)
				ez->assume(ez->expression(ezSAT::OpAnd, undef_sig));
		}

		int import_cell_counter = 0;
		for (auto cell : module->cells())
			if (design->selected(module, cell)) {
				// log("Import cell: %s\n", RTLIL::id2cstr(cell->name));
				if (satgen.importCell(cell, timestep)) {
					for (auto &p : cell->connections())
						if (ct.cell_output(cell->type, p.first))
							show_drivers.insert(sigmap(p.second), cell);
					import_cell_counter++;
				} else if (ignore_unknown_cells)
					log_warning("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
				else
					log_error("Failed to import cell %s (type %s) to SAT database.\n", RTLIL::id2cstr(cell->name), RTLIL::id2cstr(cell->type));
		}
		log("Imported %d cells to SAT database.\n", import_cell_counter);

		if (set_assumes) {
			RTLIL::SigSpec assumes_a, assumes_en;
			satgen.getAssumes(assumes_a, assumes_en, timestep);
			for (int i = 0; i < GetSize(assumes_a); i++)
				log("Import constraint from assume cell: %s when %s.\n", log_signal(assumes_a[i]), log_signal(assumes_en[i]));
			ez->assume(satgen.importAssumes(timestep));
		}

		if (initstate)
		{
			RTLIL::SigSpec big_lhs, big_rhs, forced_def;

			// Check for $anyinit cells that are forced to be defined
			if (set_init_undef && satgen.def_formal)
				for (auto cell : module->cells())
					if (cell->type == ID($anyinit))
						forced_def.append(sigmap(cell->getPort(ID::Q)));

			for (auto wire : module->wires())
			{
				if (wire->attributes.count(ID::init) == 0)
					continue;

				RTLIL::SigSpec lhs = sigmap(wire);
				RTLIL::SigSpec rhs = wire->attributes.at(ID::init);
				log_assert(lhs.size() == rhs.size());

				RTLIL::SigSpec removed_bits;
				for (int i = 0; i < lhs.size(); i++) {
					RTLIL::SigSpec bit = lhs.extract(i, 1);
					if (rhs[i] == State::Sx || !satgen.initial_state.check_all(bit)) {
						if (rhs[i] != State::Sx)
							removed_bits.append(bit);
						lhs.remove(i, 1);
						rhs.remove(i, 1);
						i--;
					}
				}

				if (removed_bits.size())
					log_warning("ignoring initial value on non-register: %s\n", log_signal(removed_bits));

				if (lhs.size()) {
					log("Import set-constraint from init attribute: %s = %s\n", log_signal(lhs), log_signal(rhs));
					big_lhs.remove2(lhs, &big_rhs);
					big_lhs.append(lhs);
					big_rhs.append(rhs);
				}
			}

			for (auto &s : sets_init)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs set expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs set expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Set expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import init set-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			if (!satgen.initial_state.check_all(big_lhs)) {
				RTLIL::SigSpec rem = satgen.initial_state.remove(big_lhs);
				log_cmd_error("Found -set-init bits that are not part of the initial_state: %s\n", log_signal(rem));
			}

			if (set_init_def) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				std::vector<int> undef_rem = satgen.importUndefSigSpec(rem, 1);
				ez->assume(ez->NOT(ez->expression(ezSAT::OpOr, undef_rem)));
			}

			if (set_init_undef) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				rem.remove(big_lhs);
				rem.remove(forced_def);
				big_lhs.append(rem);
				big_rhs.append(RTLIL::SigSpec(RTLIL::State::Sx, rem.size()));
			}

			if (set_init_zero) {
				RTLIL::SigSpec rem = satgen.initial_state.export_all();
				rem.remove(big_lhs);
				big_lhs.append(rem);
				big_rhs.append(RTLIL::SigSpec(RTLIL::State::S0, rem.size()));
			}

			if (big_lhs.size() == 0) {
				log("No constraints for initial state found.\n\n");
				return;
			}

			log("Final init constraint equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
			check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
			ez->assume(satgen.signals_eq(big_lhs, big_rhs, timestep));
		}
	}

	int setup_proof(int timestep = -1)
	{
		log_assert(prove.size() || prove_x.size() || prove_asserts);

		RTLIL::SigSpec big_lhs, big_rhs;
		std::vector<int> prove_bits;

		if (prove.size() > 0)
		{
			for (auto &s : prove)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs proof expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs proof expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Proof expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import proof-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			log("Final proof equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));
			check_undef_enabled(big_lhs), check_undef_enabled(big_rhs);
			prove_bits.push_back(satgen.signals_eq(big_lhs, big_rhs, timestep));
		}

		if (prove_x.size() > 0)
		{
			for (auto &s : prove_x)
			{
				RTLIL::SigSpec lhs, rhs;

				if (!RTLIL::SigSpec::parse_sel(lhs, design, module, s.first))
					log_cmd_error("Failed to parse lhs proof-x expression `%s'.\n", s.first.c_str());
				if (!RTLIL::SigSpec::parse_rhs(lhs, rhs, module, s.second))
					log_cmd_error("Failed to parse rhs proof-x expression `%s'.\n", s.second.c_str());
				show_signal_pool.add(sigmap(lhs));
				show_signal_pool.add(sigmap(rhs));

				if (lhs.size() != rhs.size())
					log_cmd_error("Proof-x expression with different lhs and rhs sizes: %s (%s, %d bits) vs. %s (%s, %d bits)\n",
						s.first.c_str(), log_signal(lhs), lhs.size(), s.second.c_str(), log_signal(rhs), rhs.size());

				log("Import proof-x-constraint: %s = %s\n", log_signal(lhs), log_signal(rhs));
				big_lhs.remove2(lhs, &big_rhs);
				big_lhs.append(lhs);
				big_rhs.append(rhs);
			}

			log("Final proof-x equation: %s = %s\n", log_signal(big_lhs), log_signal(big_rhs));

			std::vector<int> value_lhs = satgen.importDefSigSpec(big_lhs, timestep);
			std::vector<int> value_rhs = satgen.importDefSigSpec(big_rhs, timestep);

			std::vector<int> undef_lhs = satgen.importUndefSigSpec(big_lhs, timestep);
			std::vector<int> undef_rhs = satgen.importUndefSigSpec(big_rhs, timestep);

			for (size_t i = 0; i < value_lhs.size(); i++)
				prove_bits.push_back(ez->OR(undef_lhs.at(i), ez->AND(ez->NOT(undef_rhs.at(i)), ez->NOT(ez->XOR(value_lhs.at(i), value_rhs.at(i))))));
		}

		if (prove_asserts) {
			RTLIL::SigSpec asserts_a, asserts_en;
			satgen.getAsserts(asserts_a, asserts_en, timestep);
			for (int i = 0; i < GetSize(asserts_a); i++)
				log("Import proof for assert: %s when %s.\n", log_signal(asserts_a[i]), log_signal(asserts_en[i]));
			prove_bits.push_back(satgen.importAsserts(timestep));
		}

		return ez->expression(ezSAT::OpAnd, prove_bits);
	}

	void force_unique_state(int timestep_from, int timestep_to)
	{
		RTLIL::SigSpec state_signals = satgen.initial_state.export_all();
		for (int i = timestep_from; i < timestep_to; i++)
			ez->assume(ez->NOT(satgen.signals_eq(state_signals, state_signals, i, timestep_to)));
	}

	bool solve(const std::vector<int> &assumptions)
	{
		log_assert(gotTimeout == false);
		ez->setSolverTimeout(timeout);
		bool success = ez->solve(modelExpressions, modelValues, assumptions);
		if (ez->getSolverTimoutStatus())
			gotTimeout = true;
		return success;
	}

	bool solve(int a = 0, int b = 0, int c = 0, int d = 0, int e = 0, int f = 0)
	{
		log_assert(gotTimeout == false);
		ez->setSolverTimeout(timeout);
		bool success = ez->solve(modelExpressions, modelValues, a, b, c, d, e, f);
		if (ez->getSolverTimoutStatus())
			gotTimeout = true;
		return success;
	}

	struct ModelBlockInfo {
		int timestep, offset, width;
		std::string description;
		bool operator < (const ModelBlockInfo &other) const {
			if (timestep != other.timestep)
				return timestep < other.timestep;
			if (description != other.description)
				return description < other.description;
			if (offset != other.offset)
				return offset < other.offset;
			if (width != other.width)
				return width < other.width;
			return false;
		}
	};

	std::vector<int> modelExpressions;
	std::vector<bool> modelValues;
	std::set<ModelBlockInfo> modelInfo;

	void maximize_undefs()
	{
		log_assert(enable_undef);
		std::vector<bool> backupValues;

		while (1)
		{
			std::vector<int> must_undef, maybe_undef;

			for (size_t i = 0; i < modelExpressions.size()/2; i++)
				if (modelValues.at(modelExpressions.size()/2 + i))
					must_undef.push_back(modelExpressions.at(modelExpressions.size()/2 + i));
				else
					maybe_undef.push_back(modelExpressions.at(modelExpressions.size()/2 + i));

			backupValues.swap(modelValues);
			if (!solve(ez->expression(ezSAT::OpAnd, must_undef), ez->expression(ezSAT::OpOr, maybe_undef)))
				break;
		}

		backupValues.swap(modelValues);
	}

	void generate_model()
	{
		RTLIL::SigSpec modelSig;
		modelExpressions.clear();
		modelInfo.clear();

		// Add "show" signals or alternatively the leaves on the input cone on all set and prove signals

		if (shows.size() == 0)
		{
			SigPool queued_signals, handled_signals, final_signals;
			queued_signals = show_signal_pool;
			while (queued_signals.size() > 0) {
				RTLIL::SigSpec sig = queued_signals.export_one();
				queued_signals.del(sig);
				handled_signals.add(sig);
				std::set<RTLIL::Cell*> drivers = show_drivers.find(sig);
				if (drivers.size() == 0) {
					final_signals.add(sig);
				} else {
					for (auto &d : drivers)
					for (auto &p : d->connections()) {
						if (d->type == ID($dff) && p.first == ID::CLK)
							continue;
						if (d->type.begins_with("$_DFF_") && p.first == ID::C)
							continue;
						queued_signals.add(handled_signals.remove(sigmap(p.second)));
					}
				}
			}
			modelSig = final_signals.export_all();

			// additionally add all set and prove signals directly
			// (it improves user confidence if we write the constraints back ;-)
			modelSig.append(show_signal_pool.export_all());
		}
		else
		{
			for (auto &s : shows) {
				RTLIL::SigSpec sig;
				if (!RTLIL::SigSpec::parse_sel(sig, design, module, s))
					log_cmd_error("Failed to parse show expression `%s'.\n", s.c_str());
				log("Import show expression: %s\n", log_signal(sig));
				modelSig.append(sig);
			}
		}

		modelSig.sort_and_unify();
		// log("Model signals: %s\n", log_signal(modelSig));

		std::vector<int> modelUndefExpressions;

		for (auto &c : modelSig.chunks())
			if (c.wire != NULL)
			{
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;
				info.width = chunksig.size();
				info.description = log_signal(chunksig);

				for (int timestep = -1; timestep <= max_timestep; timestep++)
				{
					if ((timestep == -1 && max_timestep > 0) || timestep == 0)
						continue;

					info.timestep = timestep;
					info.offset = modelExpressions.size();
					modelInfo.insert(info);

					std::vector<int> vec = satgen.importSigSpec(chunksig, timestep);
					modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());

					if (enable_undef) {
						std::vector<int> undef_vec = satgen.importUndefSigSpec(chunksig, timestep);
						modelUndefExpressions.insert(modelUndefExpressions.end(), undef_vec.begin(), undef_vec.end());
					}
				}
			}

		// Add initial state signals as collected by satgen
		//
		modelSig = satgen.initial_state.export_all();
		for (auto &c : modelSig.chunks())
			if (c.wire != NULL)
			{
				ModelBlockInfo info;
				RTLIL::SigSpec chunksig = c;

				info.timestep = 0;
				info.offset = modelExpressions.size();
				info.width = chunksig.size();
				info.description = log_signal(chunksig);
				modelInfo.insert(info);

				std::vector<int> vec = satgen.importSigSpec(chunksig, 1);
				modelExpressions.insert(modelExpressions.end(), vec.begin(), vec.end());

				if (enable_undef) {
					std::vector<int> undef_vec = satgen.importUndefSigSpec(chunksig, 1);
					modelUndefExpressions.insert(modelUndefExpressions.end(), undef_vec.begin(), undef_vec.end());
				}
			}

		modelExpressions.insert(modelExpressions.end(), modelUndefExpressions.begin(), modelUndefExpressions.end());
	}

	void print_model()
	{
		int maxModelName = 10;
		int maxModelWidth = 10;

		for (auto &info : modelInfo) {
			maxModelName = max(maxModelName, int(info.description.size()));
			maxModelWidth = max(maxModelWidth, info.width);
		}

		log("\n");

		int last_timestep = -2;
		for (auto &info : modelInfo)
		{
			RTLIL::Const value;
			bool found_undef = false;

			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx, found_undef = true;
			}

			if (info.timestep != last_timestep) {
				const char *hline = "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------"
						    "---------------------------------------------------------------------------------------------------";
				if (last_timestep == -2) {
					log(max_timestep > 0 ? "  Time " : "  ");
					log("%-*s %11s %9s %*s\n", maxModelName+5, "Signal Name", "Dec", "Hex", maxModelWidth+3, "Bin");
				}
				log(max_timestep > 0 ? "  ---- " : "  ");
				log("%*.*s %11.11s %9.9s %*.*s\n", maxModelName+5, maxModelName+5,
						hline, hline, hline, maxModelWidth+3, maxModelWidth+3, hline);
				last_timestep = info.timestep;
			}

			if (max_timestep > 0) {
				if (info.timestep > 0)
					log("  %4d ", info.timestep);
				else
					log("  init ");
			} else
				log("  ");

			if (info.width <= 32 && !found_undef)
				log("%-*s %11d %9x %*s\n", maxModelName+5, info.description.c_str(), value.as_int(), value.as_int(), maxModelWidth+3, value.as_string().c_str());
			else
				log("%-*s %11s %9s %*s\n", maxModelName+5, info.description.c_str(), "--", "--", maxModelWidth+3, value.as_string().c_str());
		}

		if (last_timestep == -2)
			log("  no model variables selected for display.\n");
	}

	void dump_model_to_vcd(std::string vcd_file_name)
	{
		rewrite_filename(vcd_file_name);
		FILE *f = fopen(vcd_file_name.c_str(), "w");
		if (!f)
			log_cmd_error("Can't open output file `%s' for writing: %s\n", vcd_file_name.c_str(), strerror(errno));

		log("Dumping SAT model to VCD file %s\n", vcd_file_name.c_str());

		time_t timestamp;
		struct tm* now;
		char stime[128] = {};
		time(&timestamp);
		now = localtime(&timestamp);
		strftime(stime, sizeof(stime), "%c", now);

		std::string module_fname = "unknown";
		auto apos = module->attributes.find(ID::src);
		if(apos != module->attributes.end())
			module_fname = module->attributes[ID::src].decode_string();

		fprintf(f, "$date\n");
		fprintf(f, "    %s\n", stime);
		fprintf(f, "$end\n");
		fprintf(f, "$version\n");
		fprintf(f, "    Generated by %s\n", yosys_version_str);
		fprintf(f, "$end\n");
		fprintf(f, "$comment\n");
		fprintf(f, "    Generated from SAT problem in module %s (declared at %s)\n",
			module->name.c_str(), module_fname.c_str());
		fprintf(f, "$end\n");

		// VCD has some limits on internal (non-display) identifier names, so make legal ones
		std::map<std::string, std::string> vcdnames;

		fprintf(f, "$scope module %s $end\n", module->name.c_str());
		for (auto &info : modelInfo)
		{
			if (vcdnames.find(info.description) != vcdnames.end())
				continue;

			char namebuf[16];
			snprintf(namebuf, sizeof(namebuf), "v%d", static_cast<int>(vcdnames.size()));
			vcdnames[info.description] = namebuf;

			// Even display identifiers can't use some special characters
			std::string legal_desc = info.description.c_str();
			for (auto &c : legal_desc) {
				if(c == '$')
					c = '_';
				if(c == ':')
					c = '_';
			}

			fprintf(f, "$var wire %d %s %s $end\n", info.width, namebuf, legal_desc.c_str());

			// Need to look at first *two* cycles!
			// We need to put a name on all variables but those without an initialization clause
			// have no value at timestep 0
			if(info.timestep > 1)
				break;
		}
		fprintf(f, "$upscope $end\n");
		fprintf(f, "$enddefinitions $end\n");
		fprintf(f, "$dumpvars\n");

		static const char bitvals[] = "01xzxx";

		int last_timestep = -2;
		for (auto &info : modelInfo)
		{
			RTLIL::Const value;

			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx;
			}

			if (info.timestep != last_timestep) {
				if(last_timestep == 0)
					fprintf(f, "$end\n");
				else
					fprintf(f, "#%d\n", info.timestep);
				last_timestep = info.timestep;
			}

			if(info.width == 1) {
				fprintf(f, "%c%s\n", bitvals[value.bits[0]], vcdnames[info.description].c_str());
			} else {
				fprintf(f, "b");
				for(int k=info.width-1; k >= 0; k --)	//need to flip bit ordering for VCD
					fprintf(f, "%c", bitvals[value.bits[k]]);
				fprintf(f, " %s\n", vcdnames[info.description].c_str());
			}
		}

		if (last_timestep == -2)
			log("  no model variables selected for display.\n");

		fprintf(f, "#%d\n", last_timestep+1);
		fclose(f);
	}

	void dump_model_to_json(std::string json_file_name)
	{
		rewrite_filename(json_file_name);
		FILE *f = fopen(json_file_name.c_str(), "w");
		if (!f)
			log_cmd_error("Can't open output file `%s' for writing: %s\n", json_file_name.c_str(), strerror(errno));

		log("Dumping SAT model to WaveJSON file '%s'.\n", json_file_name.c_str());

		int mintime = 1, maxtime = 0, maxwidth = 0;;
		dict<string, pair<int, dict<int, Const>>> wavedata;

		for (auto &info : modelInfo)
		{
			Const value;
			for (int i = 0; i < info.width; i++) {
				value.bits.push_back(modelValues.at(info.offset+i) ? RTLIL::State::S1 : RTLIL::State::S0);
				if (enable_undef && modelValues.at(modelExpressions.size()/2 + info.offset + i))
					value.bits.back() = RTLIL::State::Sx;
			}

			wavedata[info.description].first = info.width;
			wavedata[info.description].second[info.timestep] = value;
			mintime = min(mintime, info.timestep);
			maxtime = max(maxtime, info.timestep);
			maxwidth = max(maxwidth, info.width);
		}

		fprintf(f, "{ \"signal\": [");
		bool fist_wavedata = true;
		for (auto &wd : wavedata)
		{
			fprintf(f, "%s", fist_wavedata ? "\n" : ",\n");
			fist_wavedata = false;

			vector<string> data;
			string name = wd.first.c_str();
			while (name.compare(0, 1, "\\") == 0)
				name = name.substr(1);

			fprintf(f, "    { \"name\": \"%s\", \"wave\": \"", name.c_str());
			for (int i = mintime; i <= maxtime; i++) {
				if (wd.second.second.count(i)) {
					string this_data = wd.second.second[i].as_string();
					char ch = '=';
					if (wd.second.first == 1)
						ch = this_data[0];
					if (!data.empty() && data.back() == this_data) {
						fprintf(f, ".");
					} else {
						data.push_back(this_data);
						fprintf(f, "%c", ch);
					}
				} else {
					data.push_back("");
					fprintf(f, "4");
				}
			}
			if (wd.second.first != 1) {
				fprintf(f, "\", \"data\": [");
				for (int i = 0; i < GetSize(data); i++)
					 fprintf(f, "%s\"%s\"", i ? ", " : "", data[i].c_str());
				fprintf(f, "] }");
			} else {
				fprintf(f, "\" }");
			}
		}
		fprintf(f, "\n  ],\n");
		fprintf(f, "  \"config\": {\n");
		fprintf(f, "    \"hscale\": %.2f\n", maxwidth / 4.0);
		fprintf(f, "  }\n");
		fprintf(f, "}\n");
		fclose(f);
	}

	void invalidate_model(bool max_undef)
	{
		std::vector<int> clause;
		if (enable_undef) {
			for (size_t i = 0; i < modelExpressions.size()/2; i++) {
				int bit = modelExpressions.at(i), bit_undef = modelExpressions.at(modelExpressions.size()/2 + i);
				bool val = modelValues.at(i), val_undef = modelValues.at(modelExpressions.size()/2 + i);
				if (!max_undef || !val_undef)
					clause.push_back(val_undef ? ez->NOT(bit_undef) : val ? ez->NOT(bit) : bit);
			}
		} else
			for (size_t i = 0; i < modelExpressions.size(); i++)
				clause.push_back(modelValues.at(i) ? ez->NOT(modelExpressions.at(i)) : modelExpressions.at(i));
		ez->assume(ez->expression(ezSAT::OpOr, clause));
	}
};

YOSYS_NAMESPACE_END

#endif
