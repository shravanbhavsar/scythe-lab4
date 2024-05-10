from pprint import pprint

from sketches.two_phase_commit_sketch import sketch as sketch_2pc
from sketches.two_phase_commit_sketch import config as config_2pc
from sketches.two_phase_commit_sketch import const as const_2pc
from sketches.two_phase_commit_sketch import assumes as assumes_2pc
from sketches.two_phase_commit_sketch import act_params as act_params_2pc
from sketches.two_phase_commit_sketch import holes as holes_2pc

from experiments_common import mk_run_experiment, mk_k_holes

OPTIMIZE = True

def mk_run_experiment_2pc(holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_2pc, holes_2pc, holes_to_poke, 
        const_2pc, assumes_2pc, 
        "two_phase_commit", config_2pc, act_params_2pc, 
        learner="naive",
        timeout=timeout,
        optimize=optimize
        )

if __name__ == "__main__":
    keys = list(holes_2pc.keys())
    # pprint(keys)
    # pprint(holes_2pc)
    holess = [[hole] for hole in holes_2pc]
    # holess = [["__Go2_g1__"]]
    # holess = [
    #     ["__Go1_g0__"],
    #     ["__Go1_g1__"],
    #     ["__Go2_g0__"],
    #     ["__Go2_g1__"],
    # ]
    # holess = mk_k_holes(holes_2pc, 2)
    # holess = [['__Go2_g1__']]
    # holess = [['__Go2_g0__']]
    holess = [['__Go2_g0__', '__Go2_g1__']]
    # holess = [['__Go2_g1__', '__Go2_go_abort__']]
    # holess = [[
    #     '__Go1_g0__', '__Go1_g1__', 
    #     '__Go2_g0__', '__Go2_g1__', '__Go2_go_abort__']]
    # holess = [['__Vote1(n)_vote_yes__', '__Commit(n)_decide_commit__']]
    holes_data = dict()
    for holes_to_poke in holess:
        # pprint(holes_2pc[holes_to_poke[0]]["functar"][-1])
        # assert(False)
        # input("Press enter to continue")
        holes_to_poke = sorted(holes_to_poke, key=lambda x: keys.index(x))
        print(f"Running 2pc experiment with holes {holes_to_poke}")
        data = mk_run_experiment_2pc(holes_to_poke, optimize=OPTIMIZE)
        holes_data[tuple(holes_to_poke)] = data
        print()
