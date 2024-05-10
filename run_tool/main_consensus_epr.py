from pprint import pprint
from sketches.consensus_epr_sketch import holes as holes_consensus_epr
from sketches.consensus_epr_sketch import config as config_consensus_epr
from sketches.consensus_epr_sketch import config2 as config_consensus_epr2
from sketches.consensus_epr_sketch import sketch as sketch_consensus_epr
from sketches.consensus_epr_sketch import const as const_consensus_epr
from sketches.consensus_epr_sketch import act_params as act_params_consensus_epr
from sketches.consensus_epr_sketch import assumes as assumes_consensus_epr

from experiments_common import mk_run_experiment, mk_k_holes

def mk_run_experiment_consensus_epr(holes_to_poke, timeout=None, optimize=None):
    return mk_run_experiment(
        sketch_consensus_epr, holes_consensus_epr, holes_to_poke, 
        const_consensus_epr, assumes_consensus_epr, 
        "consensus_epr", config_consensus_epr, act_params_consensus_epr,
        learner="naive",
        timeout=timeout,
        tla_config2=config_consensus_epr2,
        optimize=optimize
    )

if __name__ == "__main__":
    # holess = [[hole] for hole in holes_consensus_epr.keys() if not holes_consensus_epr[hole]["is_guard"]]
    holess = [[hole] for hole in holes_consensus_epr.keys()]
    # __IgnoreRequestVote(src, dst)_vote_msg__	__IgnoreRequestVote(src, dst)_voted__	__IgnoreRequestVote(src, dst)_votes__	__IgnoreRequestVote(src, dst)_decided__	__IgnoreRequestVote(src, dst)_leader__	__SendVote(src, dst)_g0__	__SendVote(src, dst)_g1__	__SendVote(src, dst)_vote_request_msg__
    holess = [["__IgnoreRequestVote(src, dst)_vote_msg__", "__IgnoreRequestVote(src, dst)_voted__", "__IgnoreRequestVote(src, dst)_votes__", "__IgnoreRequestVote(src, dst)_decided__", "__IgnoreRequestVote(src, dst)_leader__", "__SendVote(src, dst)_g0__", "__SendVote(src, dst)_g1__", "__SendVote(src, dst)_vote_request_msg__"]]
    for holes in holess:
        pprint( holes_consensus_epr[holes[0]]["functar"][-1])
        # assert(False)
        print(f"Running consensus epr experiment with holes {holes}")
        mk_run_experiment_consensus_epr(holes)
