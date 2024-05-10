from pathlib import Path
from pprint import pprint
from pprint import pprint
import json

from .mk_sketch import mild_ground_truth_parsing

dir_path = Path(__file__).parent.absolute()
sketch = open(dir_path / 'full_2pc_sketch.tla', "r").read()
config = open(dir_path / 'full_2pc.cfg', "r").read()

const = [("n1", "Int"), ("n2", "Int"), ("n3", "Int"), ("Node", ("Set", "Int"))]

assumes = [
    ["!=", "n1", "n2", "n3"],
    ["=", 
        "Node", 
        ["set.union", 
         ["set.singleton", "n1"], 
         ["set.singleton", "n2"], 
         ["set.singleton", "n3"]]],
]

act_params = {
    "Initial predicate" : [],
    "SubmitTransaction" : [],
    "AcceptDecision" : [],
    "MkCompatible" : ["n"],
    "MkIncompatible" : ["n"],
    "ResetDatabaseManager" : ["n"],
    "VoteYes" : ["n"],
    "VoteNo" : ["n"],
    "Commit" : ["n"],
    "Abort" : ["n"],
    "InitiateVote" : ["n"],
    "DecideCommit" : [],
    "DecideAbort" : [],
    "SetResetFlag" : [],
    "ResetTransactionManager" : []
}

IS_FAIR = {
    k : True for k in act_params.keys() 
    if k not in ["MkCompatible", "MkIncompatible"]}

PARAM_MAPS = {
    k : [
        {'n' : 'n1',},
        {'n' : 'n2',},
        {'n' : 'n3',},
    ] if act_params[k] == ["n"] else [dict()] for k in act_params.keys()}

PROCESS_DEPENDS = {
    "db_man" : [
        ["aborted", ("Set", "Int")],
        ["committed", ("Set", "Int")],
        ["compatible", ("Set", "Int")],
        ["frozen", ("Set", "Int")],
        ["reset_flag", "Bool"],
        ["to_abort", ("Set", "Int")],
        ["to_commit", ("Set", "Int")],
        ["to_vote", ("Set", "Int")],
        ["voted_no", ("Set", "Int")],
        ["voted_yes", ("Set", "Int")],
    ]
}

DEPENDS = {
    "VoteYes" : PROCESS_DEPENDS["db_man"],
    "VoteNo" : PROCESS_DEPENDS["db_man"],
    "Commit" : PROCESS_DEPENDS["db_man"],
    "Abort" : PROCESS_DEPENDS["db_man"],
    "ResetDatabaseManager" : PROCESS_DEPENDS["db_man"],
}

def mk_start_body(atom_map, sort, update_var, nt_suffix):
    start_body = []

    nt_suffix = ""
    nt_map = dict()
    if "Bool" in atom_map:
        nt_map["Bool"] = f"Bool{nt_suffix}"
    if "Int" in atom_map:
        nt_map["Int"] = f"Int{nt_suffix}"
    if ("Set", "Int") in atom_map:
        nt_map[("Set", "Int")] = f"SetInt{nt_suffix}"
    nt_map["Start"] = f"Start{nt_suffix}"

    if sort == "Bool":
        start_body = [
            ["set.member", nt_map["Int"], nt_map[("Set", "Int")]],
            ["not", ["set.member", nt_map["Int"], nt_map[("Set", "Int")]]],
        ]
        if "Bool" in atom_map:
            start_body = [nt_map["Bool"]] + start_body
    elif sort == ("Set", "Int"):
        if update_var is not None:
            start_body = [
                # update_var[0],
                ["set.union", update_var[0], ["set.singleton", nt_map["Int"]]],
                ["set.minus", update_var[0], ["set.singleton", nt_map["Int"]]],
            ]
        else:
            raise ValueError("update_var must be specified if sort is Set")
    return start_body, nt_map

def mk_grammar(fn_name, depends, sort, update_var):
    # return None
    atom_map = dict()
    for k, v in depends:
        if v not in atom_map:
            atom_map[v] = []
        atom_map[v].append(k)
    start_body, nt_map = mk_start_body(
        atom_map, sort, update_var=update_var, nt_suffix=fn_name)
    grammar = [
        [nt_map['Start'], sort, start_body]
    ]
    for k, v in atom_map.items():
        grammar.append([nt_map[k], k, v])
    return grammar

def mk_depends(action, update_var):
    if (
        update_var is None
        # or True # if this line is uncommented, the runtime is much slower
            ):
        res = list(list(x) for x in DEPENDS[action])
    else:
        res = [update_var]
    if "n" in act_params[action]:
        res.append(["n", "Int"])
    return res

def mk_functar(k, action, update_var):
    depends = mk_depends(action, update_var=update_var)
    if update_var is None:
        sort = "Bool"
    else:
        sort = update_var[-1]
    grammar = mk_grammar(k, depends, sort, update_var=update_var)
    functar = [
        k,
        depends,
        sort,
        grammar,
    ]
    return functar, grammar

def mk_kv(action, ground_truth, update_var, sub_k):
    is_guard = update_var is None
    if sub_k is None:
        if is_guard:
            raise ValueError("sub_k must be specified if update_var is None")
        sub_k = update_var[0]
    assert(sub_k is not None)
    k = f"__{action}_{sub_k}__"
    functar, grammar = mk_functar(k, action, update_var=update_var)

    hole_info = {"ufn" : k, "gt" : ground_truth}
    var_types = {
        "to_vote" : ("Set", "Int"),
        "voted_yes" : ("Set", "Int"),
        "voted_no" : ("Set", "Int"),
        "to_commit" : ("Set", "Int"),
        "committed" : ("Set", "Int"),
        "to_abort" : ("Set", "Int"),
        "aborted" : ("Set", "Int"),
        "frozen" : ("Set", "Int"),
        "compatible" : ("Set", "Int"),
        "user_waiting" : ("Set", "Int"),
        "decided" : "Bool",
        "reset_flag" : "Bool",
        "n" : "Int",
    }
    param_args = ["n"]
    default = {
        '__VoteNo_g2__' : 
            ["not", ["set.member", "n", "compatible"]],
        '__ResetDatabaseManager_g2__' : 
            ["not", ["set.member", "n", "to_abort"]],
        '__ResetDatabaseManager_g3__' : 
            ["not", ["set.member", "n", "to_commit"]],
    }

    parsed_ground_truth = mild_ground_truth_parsing(
        hole_info, var_types, param_args, default, ground_truth)

    v = {
        "functar" : functar,
        "grammar" : grammar,
        "ground_truth" : ground_truth,
        "parsed_ground_truth" : parsed_ground_truth,
        "is_guard" : is_guard,
        "action" : action,
        "is_fair" : IS_FAIR[action],
        "param_maps" : PARAM_MAPS[action],
    }
    return (k, v)

guards = {
    "VoteYes" : ["n \\in to_vote", "n \\in compatible"],
    "VoteNo" : ["n \\in to_vote", "~(n \\in compatible)"],
    "Commit" : ["n \\in to_commit"],
    "Abort" : ["n \\in to_abort"],
    "ResetDatabaseManager" : [
        "reset_flag", "~ (n \\in to_abort)", "~ (n \\in to_commit)"],
}

updates = {
    "VoteYes" : [
        (["to_vote", ("Set", "Int")], "to_vote \\ {n}"),
        (["voted_yes", ("Set", "Int")], "voted_yes \\cup {n}"),
        (["frozen", ("Set", "Int")], "frozen \\cup {n}"),
    ],
    "VoteNo" : [
        (["to_vote", ("Set", "Int")], "to_vote \\ {n}"),
        (["voted_no", ("Set", "Int")], "voted_no \\cup {n}"),
        (["frozen", ("Set", "Int")], "frozen \\cup {n}"),
    ],
    "Commit" : [
        (["to_commit", ("Set", "Int")], "to_commit \\ {n}"),
        (["committed", ("Set", "Int")], "committed \\cup {n}"),
    ],
    "Abort" : [
        (["to_abort", ("Set", "Int")], "to_abort \\ {n}"),
        (["aborted", ("Set", "Int")], "aborted \\cup {n}"),
    ],
    "ResetDatabaseManager" : [
        (["frozen", ("Set", "Int")], "frozen \\ {n}"),
        (["aborted", ("Set", "Int")], "aborted \\ {n}"),
        (["committed", ("Set", "Int")], "committed \\ {n}"),
        (["voted_yes", ("Set", "Int")], "voted_yes \\ {n}"),
        (["voted_no", ("Set", "Int")], "voted_no \\ {n}"),
    ]
}

kvs = []

for action, ground_truths in updates.items():
    for update_var, ground_truth in ground_truths:
        kv = mk_kv(action, ground_truth, update_var=update_var, sub_k=None)
        kvs.append(kv)

for action, ground_truths in guards.items():
    for idx, ground_truth in enumerate(ground_truths, 1):
        kv = mk_kv(action, ground_truth, update_var=None, sub_k=f"g{idx}")
        kvs.append(kv)

kvs = dict(kvs)

# from pprint import pprint
# pprint(kvs)

holes = kvs

if __name__ == "__main__":
    grammars = {k : v["grammar"] for k, v in kvs.items()}
    # remove the typing info from the grammars
    for k, v in grammars.items():
        for i in range(len(v)):
            v[i] = [v[i][0], v[i][2]]
    print(json.dumps(grammars, indent=2))