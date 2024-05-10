from pprint import pprint

from sketches.sharded_kv_sketch import sketch as sketch_sharded_kv
from sketches.sharded_kv_sketch import config as config_sharded_kv
from sketches.sharded_kv_sketch import const as const_sharded_kv
from sketches.sharded_kv_sketch import assumes as assumes_sharded_kv
from sketches.sharded_kv_sketch import act_params as act_params_sharded_kv
from sketches.sharded_kv_sketch import holes as holes_sharded_kv

from experiments_common import mk_run_experiment, mk_k_holes

PROTOCOLNAME = "sharded_kv"

def mk_run_experiment_sharded_kv(holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_sharded_kv, holes_sharded_kv, holes_to_poke, 
        const_sharded_kv, assumes_sharded_kv, 
        PROTOCOLNAME, config_sharded_kv, act_params_sharded_kv, 
        learner="naive",
        timeout=timeout,
        optimize=optimize
        )

if __name__ == "__main__":
    keys = list(holes_sharded_kv.keys())
    holess = [[hole] for hole in holes_sharded_kv]
    # holess = [['__Put(n, k, v)_owner__']]
    # holess = [['__Reshard(k,v,n_old,n_new)_g2__', '__Reshard(k,v,n_old,n_new)_table__', '__Reshard(k,v,n_old,n_new)_owner__', '__Reshard(k,v,n_old,n_new)_transfer_msg__']]
    # holess = [["__Reshard(k,v,n_old,n_new)_g1__", "__Reshard(k,v,n_old,n_new)_event_queue__"]]
    holess = [['__RecvTransferMsg(n, k, v)_g0__']]
    holes_data = dict()
    pprint(holes_sharded_kv.keys())
    for holes_to_poke in holess:
        pprint(holes_sharded_kv[holes_to_poke[0]]["functar"][-1])
        holes_to_poke = sorted(holes_to_poke, key=lambda x: keys.index(x))
        print(f"Running sharded_kv experiment with holes {holes_to_poke}")
        data = mk_run_experiment_sharded_kv(holes_to_poke)
        holes_data[tuple(holes_to_poke)] = data
        print()
