from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_inf_set_idiom, mk_nt, mk_set_idiom, mk_tnt

TAS : dict = {
    "Node" : ("Dom", "Node"),
}
TAS["NodeSet"] = ("Set", TAS["Node"])


def gfn_guard_rm(hole_info, return_type, var_types, param_args, default):
    keep_vars = [
        "vote_yes", "vote_no", "alive", "go_commit", "go_abort",
        "decide_commit", "decide_abort", "n", "compatible"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        ["Start", "Bool", ["(Rel set.member)", ["not", "(Rel set.member)"]]],
		mk_in_rule(depends),
    ]
    grammar += mk_atom_rules(depends, {})
    return depends, grammar

def gfn_guard_rm_inf(hole_info, return_type, var_types, param_args, default):
    keep_vars = [
        "vote_yes", "vote_no", "alive", "go_commit", "go_abort",
        "decide_commit", "decide_abort", "n", "compatible"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        ["Start", "Bool", 
            ["(Rel set.member)",
            ["not", "Start"],
            ["and", "Start", "Start"],
            ["or", "Start", "Start"]]],
		mk_in_rule(depends),
    ]
    grammar += mk_atom_rules(depends, {})
    return depends, grammar

def gfn_update_rm(hole_info, return_type, var_types, param_args, default):
    uv = hole_info["update_var"]
    keep_vars = [uv, "n"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        [*mk_tnt("Bool", wrap="Start"), 
            [mk_nt("Bool"), ("Bool", True), ("Bool", False)]],
        [*mk_tnt(TAS["NodeSet"], wrap="Start"), mk_set_idiom(TAS["Node"])],
    ]
    grammar += mk_atom_rules(depends, {})

    start_nt = mk_nt(return_type, "Start")
    starts = [r for r in grammar if r[0] == start_nt]
    if len(starts) != 1:
        raise ValueError("Expected exactly one return type. Got: ", starts)
    start = starts[0]
    rest = [r for r in grammar if r[0] != start_nt]
    grammar = [start] + rest
    return depends, grammar

def gfn_update_rm_inf(hole_info, return_type, var_types, param_args, default):
    uv = hole_info["update_var"]
    keep_vars = [uv, "n"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        [*mk_tnt("Bool", wrap="Start"), 
            [
                mk_nt("Bool"), ("Bool", True), ("Bool", False),
                ["not", mk_nt("Bool", "Start")],
                ["and", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
                ["or", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
            ]],
        mk_inf_set_idiom(TAS["NodeSet"], wrap="Start"),
    ]
    grammar += mk_atom_rules(depends, {})

    start_nt = mk_nt(return_type, "Start")
    starts = [r for r in grammar if r[0] == start_nt]
    if len(starts) != 1:
        raise ValueError("Expected exactly one return type. Got: ", starts)
    start = starts[0]
    rest = [r for r in grammar if r[0] != start_nt]
    grammar = [start] + rest
    return depends, grammar

def gfn_guard_tm(hole_info, return_type, var_types, param_args, default):
    keep_vars = [
        "vote_yes", "vote_no", "alive", "go_commit", "go_abort",
        "decide_commit", "decide_abort", "Node"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        ["Start", "Bool", ["(Rel =)", ["not", "(Rel =)"]]],
        ["(Rel =)", "Bool", [
            ["=", mk_nt(TAS["NodeSet"]), mk_nt(TAS["NodeSet"])],
        ]],
        [*mk_tnt(TAS["NodeSet"], wrap="Small"), [
            (TAS["NodeSet"], "emptyset"),
            mk_nt(TAS["NodeSet"], "Sub"),
            ["set.singleton", mk_nt(TAS["Node"])],
        ]],
        [*mk_tnt(TAS["NodeSet"]), 
            [
                mk_nt(TAS["NodeSet"], wrap="Small"),
                ["set.union", mk_nt(TAS["NodeSet"]), mk_nt(TAS["NodeSet"])],
                ["set.minus", mk_nt(TAS["NodeSet"]), mk_nt(TAS["NodeSet"])],
                ["set.intersect", mk_nt(TAS["NodeSet"]), mk_nt(TAS["NodeSet"])],
            ]],
    ]
    atom_except = [TAS["NodeSet"]]
    atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
    grammar += mk_atom_rules(depends, atom_except)
    return depends, grammar

def gfn_update_tm(hole_info, return_type, var_types, param_args, default):
    uv = hole_info["update_var"]
    keep_vars = [uv, "Node"]
    depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
    grammar = [
        [*mk_tnt("Bool", wrap="Start"), 
            [
                mk_nt("Bool"), ("Bool", True), ("Bool", False),
                ["not", mk_nt("Bool", "Start")],
                ["and", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
                ["or", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
            ]],
        # [*mk_tnt(TAS["NodeSet"], wrap="Start"), mk_set_idiom(TAS["Node"])],
        mk_inf_set_idiom(TAS["NodeSet"], wrap="Start"),
    ]
    grammar += mk_atom_rules(depends, {})
    start_nt = mk_nt(return_type, "Start")
    starts = [r for r in grammar if r[0] == start_nt]
    if len(starts) != 1:
        raise ValueError("Expected exactly one return type. Got: ", starts)
    start = starts[0]
    rest = [r for r in grammar if r[0] != start_nt]
    grammar = [start] + rest
    return depends, grammar