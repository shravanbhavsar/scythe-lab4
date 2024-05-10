
# Some type aliases
from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_inf_set_idiom, mk_inf_set_store_idiom, mk_nt, mk_set_idiom, mk_set_store_idiom, mk_store_idiom, mk_subset_rule, mk_tnt
from .mk_sketch import get_act_params


TAS = {
    "Value" : ("Dom", "Value"),
    "Node" : ("Dom", "Node"),
}
TAS["Msg"] = ("Tuple", TAS["Node"], TAS["Node"])
TAS["SetMsg"] = ("Set", TAS["Msg"])
TAS["SetValue"] = ("Set", TAS["Value"])
TAS["SetNode"] = ("Set", TAS["Node"])
TAS["SetSetNode"] = ("Set", TAS["SetNode"])
TAS["Decisions"] = ("Array", TAS["Node"], TAS["SetValue"])
TAS["Votes"] = ("Array", TAS["Node"], TAS["SetNode"])
TAS["Indicator"] = ("Array", TAS["Node"], "Bool")



def guard_gfn_aux(hole_info, var_types, param_args, grammar):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars = [v for v in keep_vars if v != "req_history"]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar += [
		mk_in_rule(depends),
		mk_eq_rule(depends),
		mk_subset_rule(depends),
		[*mk_tnt("Bool"), [
			mk_nt("Bool", "Sub"),
			["select", mk_nt(TAS["Indicator"]), "LocalNode"],
		]],
		[*mk_tnt(TAS["SetNode"]), [
			(TAS["SetNode"], "emptyset"),
			mk_nt(TAS["SetNode"], "Sub"),
			["select", mk_nt(TAS["Votes"]), "LocalNode"],
		]],
		[*mk_tnt(TAS["SetValue"]), [
			(TAS["SetValue"], "emptyset"),
			["set.singleton", mk_nt(TAS["Value"])],
			mk_nt(TAS["SetValue"], "Sub"),
			["select", mk_nt(TAS["Decisions"]), "LocalNode"],
		]],
		# For accessing local state---nodes cannot access remote state directly
		["LocalNode", TAS["Node"], [x for x in ["src", "n"] if x in keep_vars]],
	]
	atom_except = [TAS["SetNode"], TAS["SetValue"], "Bool"]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = [TAS["SetNode"], TAS["SetValue"], "Bool"]
	grammar += mk_atom_rules(
		depends, atom_except=atom_except, atom_require=atom_require)
	return depends, grammar

def guard_gfn_inf(hole_info, return_type, var_types, param_args, default):
	grammar = [
		["Start", "Bool", 
   			[
				"(Rel =)", "(Rel set.member)", "(Rel set.subset)", "Bool",
				["not", "Start"],
				["and", "Start", "Start"],
				["or", "Start", "Start"],
			]],
    ]
	return guard_gfn_aux(hole_info, var_types, param_args, grammar)

def guard_gfn_finite(hole_info, return_type, var_types, param_args, default):
	grammar = [
		["Start", "Bool", ["Start1", ["not", "Start1"]]],
		["Start1", "Bool", 
   			[
				"(Rel =)", "(Rel set.member)", "(Rel set.subset)", "Bool",
			]],
    ]
	return guard_gfn_aux(hole_info, var_types, param_args, grammar)

def update_gfn_finite(hole_info, return_type, var_types, param_args, default):
	# return gfn1(hole_info, return_type, var_types, param_args, default)
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt(TAS["SetMsg"], "Start"), 
   			mk_set_idiom(TAS["Msg"])],
		# [*mk_tnt(TAS["SetNode"], "Start"), 
   		# 	mk_set_idiom(TAS["Node"])],
		[*mk_tnt(TAS["Indicator"], "Start"),
   			mk_store_idiom(TAS["Indicator"], locals_nt="LocalNode")],
		[*mk_tnt(TAS["Votes"], "Start"), 
   			mk_set_store_idiom(TAS["Votes"], locals_nt="LocalNode")],
		[*mk_tnt(TAS["Decisions"], "Start"), 
   			mk_set_store_idiom(TAS["Decisions"], locals_nt="LocalNode")],
		[*mk_tnt("Bool"), 
   			[("Bool", True), ("Bool", False), mk_nt("Bool", "Sub")]],
		["LocalNode", TAS["Node"], [x for x in ["src", "n"] if x in keep_vars]],
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

def update_gfn_inf(hole_info, return_type, var_types, param_args, default):
	# return gfn1(hole_info, return_type, var_types, param_args, default)
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		mk_inf_set_idiom(TAS["SetMsg"], wrap="Start"),
		[*mk_tnt(TAS["Indicator"], "Start"),
   			mk_store_idiom(TAS["Indicator"], locals_nt="LocalNode")],
		*mk_inf_set_store_idiom(
			TAS["Votes"], wrap="Start", locals_nt="LocalNode"),
		*mk_inf_set_store_idiom(
			TAS["Decisions"], wrap="Start", locals_nt="LocalNode"),
		[*mk_tnt("Bool"), 
   			[
				("Bool", True), ("Bool", False), mk_nt("Bool", "Sub"),
				["select", mk_nt(TAS["Indicator"]), "LocalNode"],
				["not", "Bool"],
				["and", "Bool", "Bool"],
				["or", "Bool", "Bool"],
            ]],
		[*mk_tnt(TAS["SetNode"]), [
            mk_nt(TAS["SetNode"], "Sub"),
			["select", mk_nt(TAS["Votes"]), "LocalNode"],
        ]],
		[*mk_tnt(TAS["SetValue"]), [
            mk_nt(TAS["SetValue"], "Sub"),
			["select", mk_nt(TAS["Decisions"]), "LocalNode"],
        ]],
		["LocalNode", TAS["Node"], [x for x in ["src", "n"] if x in keep_vars]],
	]
	atom_except = ["Bool", TAS["SetNode"], TAS["SetValue"]]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = ["Bool", TAS["SetNode"], TAS["SetValue"]]
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