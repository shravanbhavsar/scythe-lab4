from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_inf_set_idiom, mk_nt, mk_set_idiom, mk_store_idiom, mk_tnt
from .mk_sketch import get_act_params, get_raw_act_name, load_sketch_meta, mk_holes, mk_init_act_params, mk_set

TAS : dict = {
    "Node" : ("Dom", "Node"),
}
TAS["SetNode"] = ("Set", TAS["Node"])
TAS["Indicator"] = ("Array", TAS["Node"], "Bool")

def guard_gfn_set(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		["Start", "Bool", ["Start1", ["not", "Start1"]]],
		["Start1", "Bool", ["Bool", "(Rel set.member)"]],
		mk_in_rule(depends),
	]
	grammar += mk_atom_rules(depends, {})
	return depends, grammar

def guard_gfn_inf_set(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		["Start", "Bool", 
            [
                "Bool", 
				"(Rel set.member)",
				["not", "Start"],
				["and", "Start", "Start"],
				["or", "Start", "Start"],
            ]],
		mk_in_rule(depends),
	]
	grammar += mk_atom_rules(depends, {})
	return depends, grammar

def guard_gfn_inf(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		["Start", "Bool", 
            [
                "Bool",
				["select", mk_nt(TAS["Indicator"]), mk_nt(TAS["Node"])],
				["not", "Start"],
				["and", "Start", "Start"],
				["or", "Start", "Start"],
            ]],
		mk_in_rule(depends),
	]
	grammar += mk_atom_rules(depends, {})
	return depends, grammar

def update_gfn_set(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"), [
			mk_nt("Bool"), ("Bool", True), ("Bool", False)]],
		[*mk_tnt(TAS["SetNode"], wrap="Start"), mk_set_idiom(TAS["Node"])],
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

def update_gfn_inf_set(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"), [
			mk_nt("Bool"), ("Bool", True), ("Bool", False),
			["not", mk_nt("Bool", "Start")],
			["and", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
			["or", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
        ]],
		# [*mk_tnt(TAS["SetNode"], wrap="Start"), mk_set_idiom(TAS["Node"])],
		mk_inf_set_idiom(TAS["SetNode"], "Start"),
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

def update_gfn_inf(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"), [
			mk_nt("Bool", "Sub"), ("Bool", True), ("Bool", False),
			["not", mk_nt("Bool", "Start")],
			["and", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
			["or", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
        ]],
		# [*mk_tnt(TAS["SetNode"], wrap="Start"), mk_set_idiom(TAS["Node"])],
		# mk_inf_set_idiom(TAS["SetNode"], "Start"),
		[*mk_tnt(TAS["Indicator"], wrap="Start"), 
            mk_store_idiom(TAS["Indicator"])],
		[*mk_tnt("Bool"), [mk_nt("Bool", "Sub"), mk_nt("Bool", "Start")]],
	]
	atom_except = ["Bool"]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = ["Bool"]
	grammar += mk_atom_rules(
		depends, atom_except=atom_except, atom_require=atom_require)
	
	start_nt = mk_nt(return_type, "Start")
	starts = [r for r in grammar if r[0] == start_nt]
	if len(starts) != 1:
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != start_nt]
	grammar = [start] + rest
	return depends, grammar	