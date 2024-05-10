from pprint import pprint
from sketches.mldr_sm_sketch import holes as holes_mldr_sm
from sketches.mldr_sm_sketch import config as config_mldr_sm
from sketches.mldr_sm_sketch import config2 as config_mldr_sm2
from sketches.mldr_sm_sketch import sketch as sketch_mldr_sm
from sketches.mldr_sm_sketch import const as const_mldr_sm
from sketches.mldr_sm_sketch import act_params as act_params_mldr_sm
from sketches.mldr_sm_sketch import assumes as assumes_mldr_sm

from experiments_common import mk_run_experiment, mk_k_holes

def mk_run_experiment_mldr_sm(
        holes_to_poke, timeout=None, optimize=None, extracheck=None):
    if extracheck:
        x = config_mldr_sm2
    else:
        x = None
    return mk_run_experiment(
        sketch_mldr_sm, holes_mldr_sm, holes_to_poke, 
        const_mldr_sm, assumes_mldr_sm, 
        "mldr_sm", config_mldr_sm, act_params_mldr_sm,
        learner="naive",
        timeout=timeout,
        tla_config2=x,
        discard_violation2=True,
        optimize=optimize
    )

if __name__ == "__main__":
    # holess = [[hole] for hole in holes_mldr_sm.keys() if not holes_mldr_sm[hole]["is_guard"]]
    holess = [[hole] for hole in holes_mldr_sm.keys()]
    # pprint(holess)
    # holess = [["__SendVote(src, dst)_g1__"]]
    # holess = mk_k_holes(list(holes_mldr_sm.keys()), 2)
    holess = [[
        "__Reconfig(i, newConfig, newVersion)_g3__",
        "__Reconfig(i, newConfig, newVersion)_g4__",
    ]]
    for holes in holess:
        pprint( holes_mldr_sm[holes[0]]["functar"][-1])
        # input("press enter")
        # assert(False)
        print(f"Running mldr_sm experiment with holes {holes}")
        mk_run_experiment_mldr_sm(holes)
