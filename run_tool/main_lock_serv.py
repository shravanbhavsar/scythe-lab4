import faulthandler
from pprint import pprint; faulthandler.enable()

from sketches.lock_serv_sketch import sketch as sketch_lock_serv
from sketches.lock_serv_sketch import config as config_lock_serv
from sketches.lock_serv_sketch import const as const_lock_serv
from sketches.lock_serv_sketch import assumes as assumes_lock_serv
from sketches.lock_serv_sketch import act_params as act_params_lock_serv
from sketches.lock_serv_sketch import holes as holes_lock_serv

from experiments_common import mk_run_experiment, mk_k_holes

OPTIMIZE = True

def mk_run_experiment_lock_serv(holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_lock_serv, holes_lock_serv, holes_to_poke, 
        const_lock_serv, assumes_lock_serv, 
        "lock_serv", config_lock_serv, act_params_lock_serv,
        learner="naive",
        timeout=timeout,
        optimize=optimize
    )

if __name__ == "__main__":
    keys = list(holes_lock_serv.keys())
    # holess = [[hole] for hole in keys]
    holess = mk_k_holes(keys, 1)
    # holess = [["__RecvGrant(n)_lock_msg__"]]
    # holess = [[
    #     '__Unlock(n)_g0__', 
    #     '__Unlock(n)_grant_msg__', 
    #     '__Unlock(n)_holds_lock__', 
    #     '__Unlock(n)_lock_msg__', 
    #     '__Unlock(n)_unlock_msg__'
    # ]]
    # holess = [['__RecvGrant(n)_g0__', '__RecvGrant(n)_grant_msg__', '__RecvGrant(n)_holds_lock__', '__RecvGrant(n)_lock_msg__']]
    holess = [['__SendLock(n)_grant_msg__', '__SendLock(n)_holds_lock__', '__SendLock(n)_unlock_msg__', '__RecvLock(n)_g0__', '__RecvLock(n)_g1__', '__RecvLock(n)_server_holds_lock__', '__RecvLock(n)_lock_msg__', '__RecvLock(n)_grant_msg__']]
    for holes in holess:
        pprint(holes_lock_serv[holes[0]]["functar"][-1])
        holes_to_poke = sorted(holes, key=lambda x: keys.index(x))
        print(f"Running lock_serv experiment with holes {holes}")
        mk_run_experiment_lock_serv(holes, optimize=OPTIMIZE)
        print()
