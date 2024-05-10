from pathlib import Path

dir_path = Path(__file__).parent.absolute()
sketch = open(dir_path / 'lock_serv_sketch.tla', "r").read()
config = open(dir_path / 'lock_serv.cfg', "r").read()

const = [("n1", "Int"), ("n2", "Int"), ("n3", "Int"), ("Node", ("Set", "Int"))]

assumes = [
    ["!=", "n1", "n2", "n3"]
]

act_params = {
    "Initial predicate" : [],
    "SendLock" : ["n"],
    "RecvLock" : ["n"],
    "RecvGrant" : ["n"],
    "Unlock" : ["n"],
    "RecvUnlock" : ["n"],
}

IS_FAIR = {k : True for k in act_params.keys()}

PARAM_MAPS = {
    k : [
        {'n' : 'n1',},
        {'n' : 'n2',},
        {'n' : 'n3',},
    ] if act_params[k] == ["n"] else [dict()] for k in act_params.keys()
}

DEPENDS = {
    "RecvLock" : [
        ["lock_msg", ("Set", "Int")],
        ["grant_msg", ("Set", "Int")],
        ["server_holds_lock", "Bool"],
    ],
    "RecvGrant" : [
        ["grant_msg", ("Set", "Int")],
        ["holds_lock", ("Set", "Int")],
    ],
    "Unlock" : [
        ["holds_lock", ("Set", "Int")],
        ["unlock_msg", ("Set", "Int")],
    ],
    "RecvUnlock" : [
        ["unlock_msg", ("Set", "Int")],
        ["server_holds_lock", "Bool"],
    ],
}

# The following 5 functions describe a /policy/ for generating grammars.

def mk_start_body(atom_map, sort, start_nt, update_var):
    start_body = []
    if sort == "Bool":
        start_body += [("Bool", True), ("Bool", False)]
        if ("Set", "Int") in atom_map:
            start_body += [
                ["set.member", "Int", str(("Set", "Int"))],
                ["not", ["set.member", "Int", str(("Set", "Int"))]],
            ]
        if "Bool" in atom_map:
            start_body = ["Bool"] + start_body
    elif sort == ("Set", "Int"):
        if update_var is not None:
            start_body = [
                # update_var[0],
                ["set.union", update_var[0], ["set.singleton", "Int"]],
                ["set.minus", update_var[0], ["set.singleton", "Int"]],
            ]
        else:
            raise ValueError("update_var must be specified if sort is Set")
    return start_body

def mk_grammar(fn_name, depends, sort, update_var=None):
    # return None
    atom_map = dict()
    for k, v in depends:
        if v not in atom_map:
            atom_map[v] = []
        atom_map[v].append(k)
    # start_nt = f'Start_{fn_name}'
    start_nt = "Start"
    start_body = mk_start_body(atom_map, sort, start_nt, update_var=update_var)
    grammar = [
        [start_nt, sort, start_body]
    ]
    for k, v in atom_map.items():
        grammar.append([str(k), k, v])
    return grammar

def mk_depends(action, update_var=None):
    if (
        update_var is None
        # or True # if this line is uncommented, the runtime is much slower
            ):
        res = list(DEPENDS[action])
    else:
        res = [update_var]
    if "n" in act_params[action]:
        res.append(["n", "Int"])
    return res

def mk_functar(k, action, update_var=None):
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

# The following 2 dictionaries configure the ground truths of each hole.
# In the case of updates, they also specify the update variable.

guards = {
    "RecvLock" : ["server_holds_lock", "n \\in lock_msg"],
    "RecvGrant" : ["n \\in grant_msg"],
    "Unlock" : ["n \\in holds_lock"],
    "RecvUnlock" : ["n \\in unlock_msg"],
}

updates = {
    "RecvLock" : [
        # [var, sort], gt
        [["server_holds_lock", "Bool"], "FALSE"],
        [["lock_msg", ("Set", "Int")], "lock_msg \\ {n}"],
        [["grant_msg", ("Set", "Int")], "grant_msg \\cup {n}"],
    ],
    "RecvGrant" : [
        [["grant_msg", ("Set", "Int")], "grant_msg \\ {n}"],
        [["holds_lock", ("Set", "Int")], "holds_lock \\cup {n}"],
    ],
    "Unlock" : [
        [["holds_lock", ("Set", "Int")], "holds_lock \\ {n}"],
        [["unlock_msg", ("Set", "Int")], "unlock_msg \\cup {n}"],
    ],
    "RecvUnlock" : [
        [["unlock_msg", ("Set", "Int")], "unlock_msg \\ {n}"],
        [["server_holds_lock", "Bool"], "TRUE"],
    ],
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

kvs = dict(kvs)

holes = kvs


if __name__ == "__main__":
    from pprint import pprint
    import json
    grammars = {k : v["grammar"] for k, v in kvs.items()}
    # remove the typing info from the grammars
    for k, v in grammars.items():
        for i in range(len(v)):
            v[i] = [v[i][0], v[i][2]]
    print(json.dumps(grammars, indent=2))