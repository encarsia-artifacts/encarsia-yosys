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
#include "../fsm/fsmdata.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

static RTLIL::Module *module;
static SigMap assign_map;
typedef std::pair<RTLIL::Cell*, RTLIL::IdString> sig2driver_entry_t;
static SigSet<sig2driver_entry_t> sig2driver, sig2user;
static std::set<RTLIL::Cell*> muxtree_cells;
static SigPool sig_at_port;

static bool check_state_mux_tree(RTLIL::SigSpec sig, pool<Cell*> &recursion_monitor, dict<RTLIL::SigSpec, bool> &mux_tree_cache)
{
	if (mux_tree_cache.find(sig) != mux_tree_cache.end())
		return mux_tree_cache.at(sig);

	if (sig.is_fully_const()) {
ret_true:
		mux_tree_cache[sig] = true;
		return true;
	}

	// TODO possibly remove
	if (sig_at_port.check_any(assign_map(sig))) {
	// if (false) {
ret_false:
		mux_tree_cache[sig] = false;
		return false;
	}

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(sig, cellport_list);
	for (auto &cellport : cellport_list)
	{
		if ((cellport.first->type != ID($mux) && cellport.first->type != ID($pmux)) || cellport.second != ID::Y) {
			if(recursion_monitor.empty()) {
				log("Wire not connected to a multiplexer!\n");
				goto ret_false;
			}
				
			log("Found leaf signal %s at depth %d\n", log_signal(sig), recursion_monitor.size());
			goto ret_true;
		}

		if (recursion_monitor.count(cellport.first)) {
			log_warning("logic loop in mux tree at signal %s in module %s.\n",
					log_signal(sig), RTLIL::id2cstr(module->name));
			goto ret_false;
		}

		recursion_monitor.insert(cellport.first);

		RTLIL::SigSpec sig_a = assign_map(cellport.first->getPort(ID::A));
		RTLIL::SigSpec sig_b = assign_map(cellport.first->getPort(ID::B));
		log("Found constituent mux %s at depth %d\n", cellport.first->name.c_str(), recursion_monitor.size());
		log("With select signal %s\n", log_signal(assign_map(cellport.first->getPort(ID::S))));

		if (!check_state_mux_tree(sig_a, recursion_monitor, mux_tree_cache)) {
			recursion_monitor.erase(cellport.first);
			goto ret_false;
		}

		for (int i = 0; i < sig_b.size(); i += sig_a.size())
			if (!check_state_mux_tree(sig_b.extract(i, sig_a.size()), recursion_monitor, mux_tree_cache)) {
				recursion_monitor.erase(cellport.first);
				goto ret_false;
			}

		recursion_monitor.erase(cellport.first);
		muxtree_cells.insert(cellport.first);
	}

	goto ret_true;
}

static bool check_state_users(RTLIL::SigSpec sig)
{
	if (sig_at_port.check_any(assign_map(sig)))
		return false;

	std::set<sig2driver_entry_t> cellport_list;
	sig2user.find(sig, cellport_list);
	for (auto &cellport : cellport_list) {
		RTLIL::Cell *cell = cellport.first;
		if ((cell->type == ID($mux) || cell->type == ID($pmux)))
			return false;
	}

	return true;
}

static void detect_fsm(RTLIL::Wire *wire, bool ignore_good_state_reg=false, bool ignore_init_attr=false, bool ignore_module_port=false, bool ignore_self_reset=false)
{
	bool has_fsm_encoding_attr = wire->attributes.count(ID::fsm_encoding) > 0 && wire->attributes.at(ID::fsm_encoding).decode_string() != "none";
	bool has_fsm_encoding_none = wire->attributes.count(ID::fsm_encoding) > 0 && wire->attributes.at(ID::fsm_encoding).decode_string() == "none";
	bool has_init_attr = wire->attributes.count(ID::init) > 0;
	bool is_module_port = sig_at_port.check_any(assign_map(RTLIL::SigSpec(wire)));
	bool looks_like_state_reg = false, looks_like_good_state_reg = false;
	bool is_self_resetting = false;

	if (has_fsm_encoding_none)
		return;

	std::set<sig2driver_entry_t> cellport_list;
	sig2driver.find(RTLIL::SigSpec(wire), cellport_list);

	// TODO this is a terrible fix
	if (RTLIL::SigSpec(wire) != assign_map(RTLIL::SigSpec(wire))){
		return;
	}

	if (GetSize(cellport_list) > 1) {
		log ("Wire %s has multiple drivers\n", log_signal(RTLIL::SigSpec(wire)));
		return;
	}
	if (GetSize(cellport_list) == 0) {
		log ("Wire %s has no drivers\n", log_signal(RTLIL::SigSpec(wire)));
		return;
	}


	for (auto &cellport : cellport_list)
	{
		if ((cellport.first->type != ID($mux) && cellport.first->type != ID($pmux)) || cellport.second != ID::Y) {
			log ("Wire %s is not driven by a multiplexer\n", log_signal(RTLIL::SigSpec(wire)));
			return;
		}
		log("Checking signal %s for a mux tree.\n", log_signal(RTLIL::SigSpec(wire)));

		muxtree_cells.clear();
		pool<Cell*> recursion_monitor;
		dict<RTLIL::SigSpec, bool> mux_tree_cache;
		RTLIL::SigSpec sig = assign_map(wire);

		looks_like_good_state_reg = check_state_users(sig);

		if (!looks_like_good_state_reg) {
			log("Signal %s is not a root of a multiplexer tree\n", log_signal(RTLIL::SigSpec(wire)));
			return;
		}

		looks_like_state_reg = check_state_mux_tree(sig, recursion_monitor, mux_tree_cache);

		// TODO change looks_like_good_state_reg to filter out signals that only go to MUXes
		if (looks_like_state_reg && looks_like_good_state_reg)
		// if (looks_like_state_reg)
		{
			log("Found an AMT root wire %s.%s.\n", log_id(wire->module), log_id(wire));
			wire->attributes[ID::fsm_encoding] = RTLIL::Const("inject");
		}
	}
	log("\n");
}

struct InjectDetectPass : public Pass {
	InjectDetectPass() : Pass("inject_detect", "finding FSMs in design") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    fsm_detect [options] [selection]\n");
		log("\n");
		log("This pass detects finite state machines by identifying the state signal.\n");
		log("The state signal is then marked by setting the attribute 'fsm_encoding'\n");
		log("on the state signal to \"auto\".\n");
		log("\n");
		log("    -ignore-good-state-reg\n");
		log("        Mark FSMs even if they don't seem to benefit from recoding\n");
		log("\n");
		log("    -ignore-init-attr\n");
		log("        Mark FSMs even if they have an initialization value\n");
		log("\n");
		log("    -ignore-module-port\n");
		log("        Mark FSMs even if they are connected to a module port\n");
		log("\n");
		log("    -ignore-self-reset\n");
		log("        Mark FSMs even if they are self-resetting\n");
		log("\n");
		log("Existing 'fsm_encoding' attributes are not changed by this pass.\n");
		log("\n");
		log("Signals can be protected from being detected by this pass by setting the\n");
		log("'fsm_encoding' attribute to \"none\".\n");
		log("\n");
		log("This pass uses a subset of FF types to detect FSMs. Run 'opt -nosdff -nodffe'\n");
		log("before this pass to prepare the design for fsm_detect.\n");
		log("\n");
#ifdef YOSYS_ENABLE_VERIFIC
		log("The Verific frontend may optimize the design in a way that interferes with FSM\n");
		log("detection. Run 'verific -cfg db_infer_wide_muxes_post_elaboration 0' before\n");
		log("reading the source, and 'bmuxmap -pmux' after 'proc' for best results.\n");
		log("\n");
#endif
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing FSM_DETECT pass (finding FSMs in design).\n");

		bool ignore_good_state_reg = false;
		bool ignore_init_attr = false;
		bool ignore_module_port = false;
		bool ignore_self_reset = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-ignore-good-state-reg") {
				ignore_good_state_reg = true;
				continue;
			}
			if (args[argidx] == "-ignore-init-attr") {
				ignore_init_attr = true;
				continue;
			}
			if (args[argidx] == "-ignore-module-port") {
				ignore_module_port = true;
				continue;
			}
			if (args[argidx] == "-ignore-self-reset") {
				ignore_self_reset = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct;
		ct.setup_internals();
		ct.setup_internals_anyinit();
		ct.setup_internals_mem();
		ct.setup_stdcells();
		ct.setup_stdcells_mem();

		for (auto mod : design->selected_modules())
		{
			module = mod;
			assign_map.set(module);

			sig2driver.clear();
			sig2user.clear();
			sig_at_port.clear();
			for (auto cell : module->cells())
				for (auto &conn_it : cell->connections()) {
					if (ct.cell_output(cell->type, conn_it.first) || !ct.cell_known(cell->type)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2driver.insert(sig, sig2driver_entry_t(cell, conn_it.first));
					}
					if (!ct.cell_known(cell->type) || ct.cell_input(cell->type, conn_it.first)) {
						RTLIL::SigSpec sig = conn_it.second;
						assign_map.apply(sig);
						sig2user.insert(sig, sig2driver_entry_t(cell, conn_it.first));
					}
				}

			for (auto wire : module->wires())
				if (wire->port_id != 0)
					sig_at_port.add(assign_map(wire));

			for (auto wire : module->selected_wires())
				detect_fsm(wire, ignore_good_state_reg, ignore_init_attr, ignore_module_port, ignore_self_reset);
		}

		assign_map.clear();
		sig2driver.clear();
		sig2user.clear();
		muxtree_cells.clear();
	}
} InjectDetectPass;

PRIVATE_NAMESPACE_END
