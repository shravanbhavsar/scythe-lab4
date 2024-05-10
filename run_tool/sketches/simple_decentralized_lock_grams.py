
from .grammar_helpers import mk_atom_rules, mk_in_rule, mk_inf_set_idiom, mk_nt, mk_select_idiom, mk_set_idiom, mk_store_idiom, mk_tnt
from .mk_sketch import get_raw_act_name

TAS : dict = {
	"Node" : ("Dom", "Node"),
}
TAS["SetNode"] = ("Set", TAS["Node"])
TAS["Message"] = ("Tuple", TAS["Node"], TAS["Node"])
TAS["SetMessage"] = ("Set", TAS["Message"])
TAS["Indicator"] = ("Array" , TAS["Node"], "Bool")

def guard_gfn(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys()]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	if get_raw_act_name(hole_info) == "Send":
		local_node = "src"
	else:
		local_node = "dst"
	grammar = [
		# ["Start", "Bool", ["(Rel set.member)", ["not", "(Rel set.member)"]]],
		# mk_in_rule(depends)
		["Start", "Bool", ["Start1", ["not", "Start1"]]],
		["Start1", "Bool", [
			"(Rel set.member)",
			["select", mk_nt(TAS["Indicator"]), "LocalNode"],
		]],
		["LocalNode", TAS["Node"], [local_node]],
		mk_in_rule(depends),
	]
	grammar += mk_atom_rules(depends, {})
	return depends, grammar

def guard_gfn_inf(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys()]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	if get_raw_act_name(hole_info) == "Send":
		local_node = "src"
	else:
		local_node = "dst"
	grammar = [
		["Start", "Bool", [
			"(Rel set.member)",
			["select", mk_nt(TAS["Indicator"]), "LocalNode"],
			["not", "Start"],
			["or", "Start", "Start"],
            ["and", "Start", "Start"],
		]],
		["LocalNode", TAS["Node"], [local_node]],
		mk_in_rule(depends),
	]
	grammar += mk_atom_rules(depends, {})
	return depends, grammar

def update_gfn(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv, "src", "dst"]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	if get_raw_act_name(hole_info) == "Send":
		local_node = "src"
	else:
		local_node = "dst"
	grammar = [
		# [*mk_tnt(TAS["SetNode"], wrap="Start"), 
   		# 	mk_set_idiom(TAS["Node"])],
		mk_inf_set_idiom(TAS["SetNode"], wrap="Start"),
		[*mk_tnt(TAS["Indicator"], wrap="Start"),
   			[
				mk_nt(TAS["Indicator"]),
				["store", mk_nt(TAS["Indicator"]), "LocalNode", mk_nt("Bool")]
			]],
		# [*mk_tnt(TAS["SetMessage"], wrap="Start"), 
   		# 	mk_set_idiom(TAS["Message"])],
		mk_inf_set_idiom(TAS["SetMessage"], wrap="Start"),
		[*mk_tnt("Bool"), 
   			[
                ("Bool", True), ("Bool", False), mk_nt("Bool", "Sub"),
                ["not", "Bool"], 
				["and", "Bool", "Bool"], 
				["or", "Bool", "Bool"],
                ]],
		["LocalNode", TAS["Node"], [local_node]],
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