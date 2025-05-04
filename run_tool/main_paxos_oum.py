#!/usr/bin/env python3
import sys
import json

from sketches.paxos_oum_sketch import sketch
from sketches.paxos_oum_sketch import config as tla_config
from sketches.paxos_oum_sketch import constants
from sketches.paxos_oum_sketch import assumes
from sketches.paxos_oum_sketch import act_params
from sketches.paxos_oum_sketch import holes

from experiments_common import mk_run_experiment

def mk_run_experiment_paxos_oum(holes_to_poke, timeout=None, optimize=False):
    return mk_run_experiment(
        sketch, holes, holes_to_poke,
        constants, assumes, "PaxosOUM",
        tla_config, act_params,
        learner="naive", logic="ALIAFS",
        timeout=timeout, optimize=optimize,
    )

def main(argv):
    # Only optional argument: optimize (0 or 1). Defaults to no optimization.
    print(f'holes: {holes}')

    optimize = False
    if len(argv) > 1:
        try:
            optimize = bool(int(argv[1]))
        except ValueError:
            print(f"Usage: {argv[0]} [optimize=0|1]")
            sys.exit(1)

    # === HARD‑CODED CONFIGURATION ===
    holes_to_poke = [
        "HOLE_Ph1a",
        "HOLE_Ph1b",
        "HOLE_Ph2a",
        "HOLE_Ph2b"
    ]
    timeout    = 1800      # seconds
    # ================================

    print(f"Running PaxosOUM synthesis with holes: {holes_to_poke}")
    data = mk_run_experiment_paxos_oum(
        holes_to_poke,
        timeout=timeout,
        optimize=optimize,
    )

    # Emit results as JSON to stdout
    print(json.dumps(data, indent=2))


if __name__ == "__main__":
    main(sys.argv)
