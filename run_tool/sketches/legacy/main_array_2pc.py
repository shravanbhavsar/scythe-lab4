from sketches.array_2pc_sketch import sketch as sketch_2pc
from sketches.array_2pc_sketch import config as config_2pc
from sketches.array_2pc_sketch import const as const_2pc
from sketches.array_2pc_sketch import assumes as assumes_2pc
from sketches.array_2pc_sketch import act_params as act_params_2pc
from sketches.array_2pc_sketch import holes as holes_2pc

from experiments_common import mk_run_experiment

def mk_run_experiment_2pc(holes_to_poke):
    mk_run_experiment(
        sketch_2pc, holes_2pc, holes_to_poke, 
        const_2pc, assumes_2pc, 
        "two_phase_commit", config_2pc, act_params_2pc,
        learner="naive"    
    )

if __name__ == "__main__":
    keys = list(holes_2pc.keys())
    holess = []
    holess = [[hole] for hole in holes_2pc]
    for holes_to_poke in holess:
        print(f"Running 2pc experiment with holes {holes_to_poke}")
        mk_run_experiment_2pc(holes_to_poke)
        print()
