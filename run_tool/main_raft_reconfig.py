from sketches.raft_reconfig_sketch import holes as holes_raft_reconfig
from sketches.raft_reconfig_sketch import config as config_raft_reconfig
from sketches.raft_reconfig_sketch import sketch as sketch_raft_reconfig
from sketches.raft_reconfig_sketch import const as const_raft_reconfig
from sketches.raft_reconfig_sketch import act_params as act_params_raft_reconfig
from sketches.raft_reconfig_sketch import assumes as assumes_raft_reconfig

from experiments_common import mk_run_experiment

def mk_run_experiment_raft_reconfig(holes_to_poke):
    mk_run_experiment(
        sketch_raft_reconfig, holes_raft_reconfig, holes_to_poke, 
        const_raft_reconfig, assumes_raft_reconfig, 
        "raft_reconfig", config_raft_reconfig, act_params_raft_reconfig)
    
if __name__ == "__main__":
    # mk_run_experiment_raft_reconfig(["__u1__"])
    mk_run_experiment_raft_reconfig(["__u2__"])