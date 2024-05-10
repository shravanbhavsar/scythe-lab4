from pprint import pprint

from sketches.peterson_sketch import sketch as sketch_peterson
from sketches.peterson_sketch import config as config_peterson
from sketches.peterson_sketch import const as const_peterson
from sketches.peterson_sketch import assumes as assumes_peterson
from sketches.peterson_sketch import act_params as act_params_peterson
from sketches.peterson_sketch import holes as holes_peterson

from experiments_common import mk_run_experiment, mk_k_holes

def mk_run_experiment_peterson(holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_peterson, holes_peterson, holes_to_poke, 
        const_peterson, assumes_peterson, 
        "peterson", config_peterson, act_params_peterson, 
        learner="naive",
        timeout=timeout,
        optimize=optimize
        )

if __name__ == "__main__":
    keys = list(holes_peterson.keys())
    holess = [[hole] for hole in holes_peterson]
    holess = [["__a3(self, other)_g1__", "__a3(self, other)_turn__", "__a3(self, other)_pc__", "__a3(self, other)_flag__"]]
    holess = [["__a3(self, other)_g1__", "__a3(self, other)_turn__"]]
    # holess = [['__a3(self, other)_turn__', '__a3(self, other)_pc__']] 
    holes_data = dict()
    for holes_to_poke in holess:
        # pprint(holes_peterson[holes_to_poke[0]]["functar"][-1])
        holes_to_poke = sorted(holes_to_poke, key=lambda x: keys.index(x))
        print(f"Running peterson experiment with holes {holes_to_poke}")
        data = mk_run_experiment_peterson(holes_to_poke)
        holes_data[tuple(holes_to_poke)] = data
        print()
