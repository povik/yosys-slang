//
// Yosys slang frontend
//
// Copyright 2024 Martin Povišer <povik@cutebit.org>
// Distributed under the terms of the ISC license, see LICENSE
//
#include "kernel/celltypes.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

PRIVATE_NAMESPACE_BEGIN
USING_YOSYS_NAMESPACE

void proc_usage(Module *mod)
{
	SigMap sigmap(mod);
	dict<SigBit, Cell*> drivers;
	dict<SigBit, SigSpec> sync_sources;

	SigSpec roots;
	for (auto proc_ : mod->processes) {
		auto proc = proc_.second;
		if (!proc->root_case.actions.empty() || !proc->root_case.switches.empty())
			log_error("Non-empty case tree in process %s\n", log_id(proc));

		for (auto sync : proc->syncs) {
			roots.append(sigmap(sync->signal));
			for (auto action : sync->actions) {
				log_assert(action.first.size() == action.second.size());
				for (int i = 0; i < action.first.size(); i++)
					sync_sources[sigmap(action.first[i])].append(sigmap(action.second[i]));
			}
		}
	}

	for (auto cell : mod->cells()) {
		if (yosys_celltypes.cell_known(cell->type)
				&& !cell->get_bool_attribute(ID::keep)
				&& !cell->type.in(ID($check), ID($print))) {
			for (const auto &conn : cell->connections())
			if (yosys_celltypes.cell_output(cell->type, conn.first))
			for (auto bit : sigmap(conn.second))
				drivers[bit] = cell;
		} else {
			for (const auto &conn : cell->connections())
				roots.append(sigmap(conn.second));
		}
	}

	for (auto w : mod->wires())
	if (w->port_output)
		roots.append(sigmap(w));

	pool<SigBit> queued;
	SigSpec queue;

	for (auto bit : roots)
	if (bit.wire && !queued.count(bit)) {
		queued.insert(bit);
		queue.append(bit);
	}

	for (int i = 0; i < queue.size(); i++) {
		SigBit bit = queue[i];

		if (drivers.count(bit)) {
			Cell *driver = drivers[bit];
			for (const auto &conn : driver->connections())
			if (yosys_celltypes.cell_input(driver->type, conn.first))
			for (auto ibit : sigmap(conn.second))
			if (ibit.wire && !queued.count(ibit)) {
				queued.insert(ibit);
				queue.append(ibit);
			}
		}

		if (sync_sources.count(bit)) {
			for (auto ibit : sigmap(sync_sources.at(bit)))
			if (ibit.wire && !queued.count(ibit)) {
				queued.insert(ibit);
				queue.append(ibit);
			}
		}
	}

	for (auto proc_ : mod->processes) {
		auto proc = proc_.second;
		for (auto sync : proc->syncs) {
			for (auto &action : sync->actions) {
				SigSig new_action;
				SigSpec removed;
				for (int i = 0; i < action.first.size(); i++) {
					SigBit tbit = sigmap(action.first[i]);
					if (queued.count(tbit)) {
						new_action.first.append(action.first[i]);
						new_action.second.append(action.second[i]);
					} else {
						removed.append(tbit);
					}
				}

				action = new_action;
				if (!removed.empty())
					log("Removed unused %s sync action target in process %s.\n",
						log_signal(removed), log_id(proc));
			}
		}
	}
}

struct ProcUsagePass : Pass {
	ProcUsagePass() : Pass("proc_usage", "analyze usage of signals assigned from processes") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    proc_usage [selection]\n");
		log("\n");
		log("This pass identifies assignments in processes which are unused outside of the\n");
		log("process of origin. As such, those assignments can be removed as a driver of\n");
		log("a module-level signal. It is important to remove those assignments ahead of the\n");
		log("`proc_dlatch` pass to not to infer spurious latches, which are a compilation\n");
		log("failure for `always_comb` blocks.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *d) override
	{
		log_header(d, "Executing PROC_USAGE pass. (analyze usage of process outputs)\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			break;
		}
		extra_args(args, argidx, d);

		for (auto mod : d->selected_whole_modules_warn())
			proc_usage(mod);
	}
} ProcUsagePass;

PRIVATE_NAMESPACE_END
