try:
    from .mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, get_act_params, get_raw_act_name
    from .mk_sketch import mk_set, mk_trivial_grammar
except:
    from mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, get_act_params, get_raw_act_name
    from mk_sketch import mk_set, mk_trivial_grammar

import itertools
from pprint import pprint
from pathlib import Path

from .two_phase_commit_grams import TAS

PREFIX = 'two_phase_commit'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

# we will not do type inference, so the user has to provide this.
VAR_TYPES = {
    "vote_yes" : TAS["NodeSet"],
    "vote_no" : TAS["NodeSet"],
    "alive" : TAS["NodeSet"],
    "go_commit" : TAS["NodeSet"],
    "go_abort" : TAS["NodeSet"],
    "decide_commit": TAS["NodeSet"],
    "decide_abort" : TAS["NodeSet"],
    "abort_flag" : "Bool",
    "compatible" : TAS["NodeSet"],
    # include quantified-over constants
    "Node" : TAS["NodeSet"],
    # include action args, but be careful
    "n" : TAS["Node"],
}

FAIR_ACTIONS = {
    "Vote1",
    "Vote2",
    "Go1",
    "Go2",
    "Commit",
    "Abort",
}

PARAM_VALS = {"n" : ["n1", "n2", "n3"]}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
MANUAL_GROUND_TRUTH = {
    "__Go1_g0__" : [
        "=", 
        ["set.intersect", "Node", "go_abort"], 
        (TAS["NodeSet"], "emptyset")],
    "__Go2_g0__" : [
        "=", 
        ["set.intersect", "Node", "go_commit"], 
        (TAS["NodeSet"], "emptyset")],
    "__Go2_g1__" : [
        "not", 
            ["=", 
            ["set.union", 
                ["set.intersect", "Node", "vote_no"], 
                ["set.minus", "Node", "alive"]], 
            (TAS["NodeSet"], "emptyset")]],
}

# Assert: for all keys in MANUAL_GROUND_TRUTH, there exists a hole in 
# META_SKETCH with the same name.
# pprint(SKETCH_META)
assert(
    all(
        any(
            hole.get("ufn", None) == k 
            for hole in SKETCH_META if "ufn" in hole) 
    for k in MANUAL_GROUND_TRUTH))

const = [
    ("n1", TAS["Node"]), ("n2", TAS["Node"]), ("n3", TAS["Node"]), 
    ("Node", TAS["NodeSet"])]

assumes = [
    ["!=", "n1", "n2", "n3"],
    ["=", "Node", mk_set(["n1", "n2", "n3"])]
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needed to be handled manually
act_params["Termination"] = []
act_params["Fail"] = ["n"]

from .two_phase_commit_grams import gfn_guard_rm_inf as gfn_guard_rm
from .two_phase_commit_grams import gfn_update_rm_inf as gfn_update_rm
from .two_phase_commit_grams import gfn_guard_tm as gfn_guard_tm
from .two_phase_commit_grams import gfn_update_tm as gfn_update_tm

def gfn(hole_info, return_type, var_types, param_args, default):

    act_name = get_raw_act_name(hole_info)
    is_guard = hole_info["update_var"] is None

    # guard + rm_action
    if is_guard and act_name in ["Vote1", "Vote2", "Commit", "Abort"]:
        return gfn_guard_rm(
            hole_info, return_type, var_types, param_args, default)
    # update + rm_action
    if not is_guard and act_name in ["Vote1", "Vote2", "Commit", "Abort"]:
        return gfn_update_rm(
            hole_info, return_type, var_types, param_args, default)
    # guard + tm_action
    if is_guard and act_name in ["Go1", "Go2"]:
        return gfn_guard_tm(
            hole_info, return_type, var_types, param_args, default)
    # update + tm_action
    if not is_guard and act_name in ["Go1", "Go2"]:
        return gfn_update_tm(
            hole_info, return_type, var_types, param_args, default)
    # guard + env_action
    # update + env_action
    assert(act_name == "Fail")
    return mk_trivial_grammar(
        hole_info, return_type, var_types, param_args, default)

from .mk_sketch import mk_trivial_grammar as gfn1

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH, gfn
)