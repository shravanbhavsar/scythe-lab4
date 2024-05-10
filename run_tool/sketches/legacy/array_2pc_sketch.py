from pathlib import Path

dir_path = Path(__file__).parent.absolute()
sketch = open(dir_path / 'array_2pc_sketch.tla', "r").read()
config = open(dir_path / 'two_phase_commit.cfg', "r").read()

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

# The user should probably not have to supply this.
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
        ["aborted", ("Array", "Int", "Bool")],
        ["committed", ("Array", "Int", "Bool")],
        ["compatible", ("Array", "Int", "Bool")],
        ["frozen", ("Array", "Int", "Bool")],
        ["reset_flag", "Bool"],
        ["to_abort", ("Array", "Int", "Bool")],
        ["to_commit", ("Array", "Int", "Bool")],
        ["to_vote", ("Array", "Int", "Bool")],
        ["voted_no", ("Array", "Int", "Bool")],
        ["voted_yes", ("Array", "Int", "Bool")],
    ]
}

DEPENDS = {
    "VoteYes" : PROCESS_DEPENDS["db_man"] + [["n", "Int"]],
    "VoteNo" : PROCESS_DEPENDS["db_man"] + [["n", "Int"]],
    "Commit" : PROCESS_DEPENDS["db_man"] + [["n", "Int"]],
    "Abort" : PROCESS_DEPENDS["db_man"] + [["n", "Int"]],
    "ResetDatabaseManager" : PROCESS_DEPENDS["db_man"] + [["n", "Int"]],
}

def mk_start_body(atom_map, sort, update_var=None):
    start_body = []
    if sort == "Bool":
        start_body = [
            ["select", str(("Array", "Int", "Bool")), "Int"],
            ["not", ["select",  str(("Array", "Int", "Bool")), "Int"]],
        ]
        if "Bool" in atom_map:
            start_body = ["Bool"] + start_body
    elif sort == ("Array", "Int", "Bool"):
        if update_var is not None:
            start_body = [
                # update_var[0],
                ["store", update_var[0], "Int", ("Bool", True)],
                ["store", update_var[0], "Int", ("Bool", False)],
            ]
        else:
            raise ValueError("update_var must be specified if sort is Set")
    return start_body

def mk_grammar(depends, sort, update_var=None):
    # return None
    atom_map = dict()
    for k, v in depends:
        if v not in atom_map:
            atom_map[v] = []
        atom_map[v].append(k)
    start_body = mk_start_body(atom_map, sort, update_var=update_var)
    grammar = [
        ['Start', sort, start_body]
    ]
    for k, v in atom_map.items():
        grammar.append([str(k), k, v])
    return grammar

def mk_functar(k, action, update_var=None):
    depends = DEPENDS[action]
    if update_var is None:
        sort = "Bool"
    else:
        sort = update_var[-1]
    grammar = mk_grammar(depends, sort, update_var=update_var)
    functar = [
        k,
        depends,
        sort,
        grammar,
    ]
    return functar

def mk_kv(action, ground_truth, update_var = None, sub_k = None):
    is_guard = update_var is None
    if sub_k is None:
        if is_guard:
            raise ValueError("sub_k must be specified if update_var is None")
        sub_k = update_var[0]
    assert(sub_k is not None)
    k = f"__{action}_{sub_k}__"
    functar = mk_functar(k, action, update_var = update_var)
    v = {
        "functar" : functar,
        "grammar" : functar[-1],
        "ground_truth" : ground_truth,
        "is_guard" : is_guard,
        "action" : action,
        "is_fair" : IS_FAIR[action],
        "param_maps" : PARAM_MAPS[action],
    }
    return (k, v)


'''Some remarks on "param maps":
Every hole exists in an action. If that action takes arguments, then
the hole may depend on those arguments. When generating constraints
corresponding to exit transitions (cycle_terms in constraint_inference.py),
the constraint inference engine needs to know about all the possible
configurations of the arguments to the action.

If the action does not take any arguments, then param_maps should be
a list with a single element, which is an empty dictionary.
I.e. param_maps = [dict()] as for __u3__ and __u4__ below.
'''

guards = {
    "VoteYes" : ["to_vote[n]", "compatible[n]"],
    "VoteNo" : ["to_vote[n]", "(~compatible[n])"],
    "Commit" : ["to_commit[n]"],
    "Abort" : ["to_abort[n]"],
    "ResetDatabaseManager" : [
        "reset_flag", "(~to_abort[n])", "(~to_commit[n])"],
}

updates = {
    "VoteYes" : [
        (("to_vote", ("Array", "Int", "Bool")), "[to_vote EXCEPT ![n] = FALSE]"),
        (("voted_yes", ("Array", "Int", "Bool")), "[voted_yes EXCEPT ![n] = TRUE]"),
        (("frozen", ("Array", "Int", "Bool")), "[frozen EXCEPT ![n] = TRUE]"),
    ],
    "VoteNo" : [
        (("to_vote", ("Array", "Int", "Bool")), "[to_vote EXCEPT ![n] = FALSE]"),
        (("voted_no", ("Array", "Int", "Bool")), "[voted_no EXCEPT ![n] = TRUE]"),
        (("frozen", ("Array", "Int", "Bool")), "[frozen EXCEPT ![n] = TRUE]"),
    ],
    "Commit" : [
        (("to_commit", ("Array", "Int", "Bool")), "[to_commit EXCEPT ![n] = FALSE]"),
        (("committed", ("Array", "Int", "Bool")), "[committed EXCEPT ![n] = TRUE]"),
    ],
    "Abort" : [
        (("to_abort", ("Array", "Int", "Bool")), "[to_abort EXCEPT ![n] = FALSE]"),
        (("aborted", ("Array", "Int", "Bool")), "[aborted EXCEPT ![n] = TRUE]"),
    ],
    "ResetDatabaseManager" : [
        (("frozen", ("Array", "Int", "Bool")), "[frozen EXCEPT ![n] = FALSE]"),
        (("aborted", ("Array", "Int", "Bool")), "[aborted EXCEPT ![n] = FALSE]"),
        (("committed", ("Array", "Int", "Bool")), "[committed EXCEPT ![n] = FALSE]"),
        (("voted_yes", ("Array", "Int", "Bool")), "[voted_yes EXCEPT ![n] = FALSE]"),
        (("voted_no", ("Array", "Int", "Bool")), "[voted_no EXCEPT ![n] = FALSE]"),
    ]
}

kvs = []

for action, ground_truths in updates.items():
    for update_var, ground_truth in ground_truths:
        kv = mk_kv(action, ground_truth, update_var = update_var)
        kvs.append(kv)

for action, ground_truths in guards.items():
    for idx, ground_truth in enumerate(ground_truths, 1):
        kv = mk_kv(action, ground_truth, update_var = None, sub_k = f"g{idx}")
        kvs.append(kv)
# from pprint import pprint
# pprint(kvs)

holes = dict(kvs)