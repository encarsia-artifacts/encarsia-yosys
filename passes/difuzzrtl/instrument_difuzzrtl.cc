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
#include "kernel/mem.h"
#include <algorithm>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

#define MAP_WIDTH 1
#define STATE_WIDTH 20
#define SUM_WIDTH 30

static bool is_flipflop(RTLIL::Cell *cell){
    return cell->type == ID($dff) || cell->type == ID($dffe) || cell->type == ID($dffsr) || cell->type == ID($dffsre) || cell->type == ID($adff) || cell->type == ID($sdff) || cell->type == ID($sdffe) || cell->type == ID($sdffce) || cell->type == ID($adffe) || cell->type == ID($aldff) || cell->type == ID($aldffe);
}

// Note: This pass does not produce _halt signals
static void difuzzrtl_reset_module(RTLIL::Design *design, RTLIL::Module *module){
    if (module->has_attribute(ID(drtl_reset))) return;

    RTLIL::Wire *meta_reset = module->addWire(RTLIL::escape_id("metaReset"));
    meta_reset->port_input = true;
    module->fixup_ports();

    for (auto cell : module->selected_cells()){
        if (is_flipflop(cell)) {
            RTLIL::SigSpec old_input = cell->getPort(ID::D);
            cell->unsetPort(ID::D);
            RTLIL::Wire *new_input = module->addWire(NEW_ID, old_input.size());
            cell->setPort(ID::D, new_input);
            module->addMux(NEW_ID, old_input, RTLIL::Const(0, old_input.size()), meta_reset, new_input);
        } else if (cell->type.isPublic()) {
            RTLIL::Module *submodule = design->module(cell->type);
            difuzzrtl_reset_module(design, submodule);
            cell->setPort(RTLIL::escape_id("metaReset"), meta_reset);
        }
    }

    module->set_bool_attribute(ID(drtl_reset));
    log("Module: %s\n", module->name.c_str());
}

static void difuzzrtl_reset(RTLIL::Design *design){
    for (auto module : design->selected_modules()) {
        difuzzrtl_reset_module(design, module);
    }
}

static void find_control_registers_rec(SigMap &sigmap, SigSet<RTLIL::Cell *> &sig2driver, std::set<RTLIL::Cell *> &recursion_monitor, std::set<RTLIL::SigSpec> &control_signals, RTLIL::SigSpec mux_select, RTLIL::SigSpec sig) {
    std::set<RTLIL::Cell *> drivers;
    sig2driver.find(sigmap(sig), drivers);
    for (auto driver : drivers) {
        if (recursion_monitor.count(driver)) continue;
        recursion_monitor.insert(driver);
        if (is_flipflop(driver)) {
            RTLIL::SigSpec output = driver->getPort(ID::Q);
            if (output.size() < STATE_WIDTH) {
                control_signals.insert(output);
            } else {
                control_signals.insert(mux_select);
            }
            continue;
        }

        for (auto &connection : driver->connections()) {
            if (driver->input(connection.first)) {
                find_control_registers_rec(sigmap, sig2driver, recursion_monitor, control_signals, mux_select, connection.second);
            }
        }
    }
    return;
}

static void find_control_registers(RTLIL::Module *module, std::set<RTLIL::SigSpec> &control_signals) {
    SigMap sigmap(module);
    SigSet<RTLIL::Cell *> sig2driver;
    std::set<RTLIL::Cell *> recursion_monitor;

    for (auto cell : module->cells()) {
        for (auto &connection : cell->connections()) {
            if (cell->output(connection.first)) {
                sig2driver.insert(sigmap(connection.second), cell);
            }
        }
    }

    for (auto cell : module->selected_cells()) {
        if (cell->type == ID($mux) || cell->type == ID($pmux)){
            RTLIL::SigSpec select = cell->getPort(ID::S);
            find_control_registers_rec(sigmap, sig2driver, recursion_monitor, control_signals, select, select);
        }
    }
}

static RTLIL::SigSpec pad(RTLIL::SigSpec signal){
    RTLIL::SigSpec padded;

    int shift = rand() % (STATE_WIDTH - signal.size() + 1);
    padded.append(RTLIL::Const(0, shift));
    padded.append(signal);
    padded.append(RTLIL::Const(0, STATE_WIDTH - padded.size()));

    return padded;
}

static RTLIL::SigSpec xor_control_registers(RTLIL::Module *module, std::set<RTLIL::SigSpec> control_signals) {
    RTLIL::SigSpec result(pad(RTLIL::Const(0, 1)));

    for (auto control_signal : control_signals) {
        RTLIL::Wire *temp = module->addWire(NEW_ID, STATE_WIDTH);
        module->addXor(NEW_ID, result, pad(control_signal), temp);
        result = RTLIL::SigSpec(temp);
    }
    return result;
}

static bool find_clock(RTLIL::Module *module, RTLIL::SigSpec &clock){
    for (auto cell : module->selected_cells()){
        if (is_flipflop(cell)) {
            clock = cell->getPort(ID::CLK);
            if (clock.is_wire()) return true;
        }
    }
    return false;
}

static void create_coverage_map(RTLIL::Module *module, RTLIL::SigSpec &clock, RTLIL::SigSpec &state, RTLIL::SigSpec &is_covered){
    RTLIL::IdString memid = module->name.str() + "_coverage_map";
    Mem mem(module, memid, MAP_WIDTH, 0, 1 << STATE_WIDTH);

    MemRd rd;
    rd.removed = false;
    rd.cell = nullptr;
    rd.clk_polarity = false;
    rd.addr = state;
    rd.data = is_covered;
    rd.init_value = Const(State::Sx, 1);
    rd.arst_value = Const(State::Sx, 1);
    rd.srst_value = Const(State::Sx, 1);
    rd.transparency_mask = std::vector<bool>(1, false);
    rd.collision_x_mask = std::vector<bool>(1, false);
    mem.rd_ports.push_back(std::move(rd));

    MemWr wr;
    wr.removed = false;
    wr.cell = nullptr;
    wr.wide_log2 = 0;
    wr.clk_enable = true;
    wr.clk_polarity = true;
    wr.priority_mask = std::vector<bool>(1, false);
    wr.clk = clock;
    wr.en = State::S1;
    wr.addr = state;
    wr.data = State::S1;
    mem.wr_ports.push_back(wr);

    mem.emit();
}

static void difuzzrtl_coverage_module(RTLIL::Design *design, RTLIL::Module *module){
    if (module->has_attribute(ID(drtl_coverage))) return;

    RTLIL::SigSpec clock;
    if (!find_clock(module, clock)) return;

    std::set<RTLIL::SigSpec> control_registers;
    find_control_registers(module, control_registers);
    if (!control_registers.size()) return;

    RTLIL::SigSpec xored_registers = xor_control_registers(module, control_registers);
    RTLIL::SigSpec state(module->addWire(module->name.str() + "_state", STATE_WIDTH));
    module->addDff(NEW_ID, clock, xored_registers, state);

    RTLIL::SigSpec is_covered(module->addWire(module->name.str() + "_is_covered", MAP_WIDTH));
    create_coverage_map(module, clock, state, is_covered);

    RTLIL::SigSpec cov_sum(module->addWire(module->name.str() + "_covSum", SUM_WIDTH));
    RTLIL::SigSpec next_sum(module->addWire(module->name.str() + "_NextSum", SUM_WIDTH));
    RTLIL::SigSpec inc_sum(module->addWire(module->name.str() + "_IncSum", SUM_WIDTH));
    module->addDff(NEW_ID, clock, next_sum, cov_sum);
    module->addMux(NEW_ID, cov_sum, inc_sum, is_covered, next_sum);
    module->addAdd(NEW_ID, cov_sum, RTLIL::Const(1, SUM_WIDTH), inc_sum);

    RTLIL::Wire *io_covsum = module->addWire(RTLIL::escape_id("io_covSum"), SUM_WIDTH);
    io_covsum->port_output = true;
    module->fixup_ports();

    RTLIL::SigSpec current_covsum = RTLIL::SigSpec(io_covsum);
    for (auto cell : module->selected_cells()){
        if (cell->type.isPublic()) {
            RTLIL::Module *submodule = design->module(cell->type);
            difuzzrtl_coverage_module(design, submodule);
            if (std::find(submodule->ports.begin(), submodule->ports.end(), RTLIL::escape_id("io_covSum")) == submodule->ports.end()) continue;

            RTLIL::SigSpec new_covsum = RTLIL::SigSpec(module->addWire(NEW_ID, SUM_WIDTH));
            RTLIL::SigSpec cell_covsum = RTLIL::SigSpec(module->addWire(NEW_ID, SUM_WIDTH));
            cell->setPort(RTLIL::escape_id("io_covSum"), cell_covsum);
            module->addAdd(NEW_ID, new_covsum, cell_covsum, current_covsum);
            current_covsum = new_covsum;
        }
    }
    module->connect(current_covsum, cov_sum);

    module->set_bool_attribute(ID(drtl_coverage));
    log("Module: %s\n", module->name.c_str());
}

static void difuzzrtl_coverage(RTLIL::Design *design){
    for (auto module : design->selected_modules()) {
        difuzzrtl_coverage_module(design, module);
    }
}

struct DifuzzRTLInstrumentPass : public Pass {
	DifuzzRTLInstrumentPass() : Pass("difuzzrtl_instrument", "instrument designs with the DifuzzRTL coverage metric") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|;
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		difuzzrtl_reset(design);
        difuzzrtl_coverage(design);
	}
} DifuzzRTLInstrumentPass;

PRIVATE_NAMESPACE_END
