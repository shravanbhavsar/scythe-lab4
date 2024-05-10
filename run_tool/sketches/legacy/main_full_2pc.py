from pprint import pprint

from sketches.full_2pc_sketch import sketch as sketch_2pc
from sketches.full_2pc_sketch import config as config_2pc
from sketches.full_2pc_sketch import const as const_2pc
from sketches.full_2pc_sketch import assumes as assumes_2pc
from sketches.full_2pc_sketch import act_params as act_params_2pc
from sketches.full_2pc_sketch import holes as holes_2pc

from experiments_common import mk_run_experiment, mk_k_holes

def mk_run_experiment_2pc(holes_to_poke, timeout=None):
    return mk_run_experiment(
        sketch_2pc, holes_2pc, holes_to_poke, 
        const_2pc, assumes_2pc, 
        "two_phase_commit", config_2pc, act_params_2pc, 
        learner="naive",
        timeout=timeout
        )

if __name__ == "__main__":
    keys = list(holes_2pc.keys())
    # holess = []
    holess = [[hole] for hole in holes_2pc]
    # holess = mk_k_holes(keys, 6)
    # holess = [["__VoteNo_g1__", "__VoteNo_g2__", "__VoteYes_g2__"]]
    # for holes_to_poke in holess[holess.index(["__VoteYes_g1__"]):]:
    holes_data = dict()
    for holes_to_poke in holess:
        holes_to_poke = sorted(holes_to_poke, key=lambda x: keys.index(x))
        print(f"Running 2pc experiment with holes {holes_to_poke}")
        data = mk_run_experiment_2pc(holes_to_poke)
        holes_data[tuple(holes_to_poke)] = data
        print()
    # pprint(holes_data)
