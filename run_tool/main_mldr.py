from pprint import pprint
from sketches.mldr_sketch import holes as holes_mldr
from sketches.mldr_sketch import config as config_mldr
from sketches.mldr_sketch import config2 as config_mldr2
from sketches.mldr_sketch import sketch as sketch_mldr
from sketches.mldr_sketch import const as const_mldr
from sketches.mldr_sketch import act_params as act_params_mldr
from sketches.mldr_sketch import assumes as assumes_mldr

from experiments_common import mk_run_experiment, mk_k_holes

def mk_run_experiment_mldr(
        holes_to_poke, timeout=None, optimize=None, extracheck=None):
    if extracheck:
        x = config_mldr2
    else:
        x = None
    return mk_run_experiment(
        sketch_mldr, holes_mldr, holes_to_poke, 
        const_mldr, assumes_mldr, 
        "mldr", config_mldr, act_params_mldr,
        learner="naive",
        timeout=timeout,
        tla_config2=x,
        discard_violation2=True,
        optimize=optimize
    )

if __name__ == "__main__":
    # holess = [[hole] for hole in holes_mldr.keys() if not holes_mldr[hole]["is_guard"]]
    holess = [[hole] for hole in holes_mldr.keys()]
    holess = [[
        "__Reconfig(i, newConfig, newVersion)_g0__",
        "__Reconfig(i, newConfig, newVersion)_g5__",
        "__Reconfig(i, newConfig, newVersion)_g6__",
        "__Reconfig(i, newConfig, newVersion)_g7__",
        "__Reconfig(i, newConfig, newVersion)_configTerm__",
        "__Reconfig(i, newConfig, newVersion)_configVersion__",
        "__Reconfig(i, newConfig, newVersion)_config__",
        "__Reconfig(i, newConfig, newVersion)_currentTerm__",
        "__Reconfig(i, newConfig, newVersion)_state__",
        "__Reconfig(i, newConfig, newVersion)_log__",
        "__Reconfig(i, newConfig, newVersion)_immediatelyCommitted__",
    ]]
    # holess = [["__SendVote(src, dst)_g1__"]]
    # holess = mk_k_holes(list(holes_mldr.keys()), 2)
    for holes in holess:
        pprint( holes_mldr[holes[0]]["functar"][-1])
        # assert(False)
        print(f"Running mldr experiment with holes {holes}")
        mk_run_experiment_mldr(holes)
