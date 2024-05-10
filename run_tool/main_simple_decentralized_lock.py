from pprint import pprint

from sketches.simple_decentralized_lock_sketch import sketch as sketch_simple_decentralized_lock
from sketches.simple_decentralized_lock_sketch import config as config_simple_decentralized_lock
from sketches.simple_decentralized_lock_sketch import const as const_simple_decentralized_lock
from sketches.simple_decentralized_lock_sketch import assumes as assumes_simple_decentralized_lock
from sketches.simple_decentralized_lock_sketch import act_params as act_params_simple_decentralized_lock
from sketches.simple_decentralized_lock_sketch import holes as holes_simple_decentralized_lock

from experiments_common import mk_run_experiment, mk_k_holes

PROTOCOLNAME = "simple_decentralized_lock"

def mk_run_experiment_simple_decentralized_lock(
        holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_simple_decentralized_lock, holes_simple_decentralized_lock, holes_to_poke, 
        const_simple_decentralized_lock, assumes_simple_decentralized_lock, 
        PROTOCOLNAME, config_simple_decentralized_lock, act_params_simple_decentralized_lock, 
        learner="naive",
        timeout=timeout,
        optimize=optimize
        )

if __name__ == "__main__":
    keys = list(holes_simple_decentralized_lock.keys())
    holess = [[hole] for hole in holes_simple_decentralized_lock]
    holess = [['__Recv(src, dst)_message__']]
    holes_data = dict()
    for holes_to_poke in holess:
        holes_to_poke = sorted(holes_to_poke, key=lambda x: keys.index(x))
        print(f"Running simple_decentralized_lock experiment with holes {holes_to_poke}")
        data = mk_run_experiment_simple_decentralized_lock(holes_to_poke)
        holes_data[tuple(holes_to_poke)] = data
        print()
