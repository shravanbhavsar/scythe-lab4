
from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_inf_set_idiom, mk_nt, mk_select_idiom, mk_set_idiom, mk_store_idiom, mk_tnt
from .mk_sketch import get_act_params


TAS = {
	"Key" : ("Dom", "Key"),
	"Val" : ("Dom", "Value"),
	"Node" : ("Dom", "Node"),
}

TAS["TabKey"] = ("Tuple", TAS["Node"], TAS["Key"])
TAS["TMsg"] = ("Tuple", TAS["Node"], TAS["Key"], TAS["Val"])
TAS["Event1"] = ("Tuple", "Int", TAS["Key"], TAS["Val"], "Int")
TAS["Event2"] = ("Tuple", "Int", TAS["Key"], TAS["Node"], TAS["Node"])
TAS["Event"] = ("Union", TAS["Event1"], TAS["Event2"])
TAS["Table"] = ("Array", TAS["TabKey"], TAS["Val"])
TAS["Owner"] = ("Array", TAS["Node"], ("Set", TAS["Key"]))
TAS["GTable"] = ("Array", TAS["Key"], TAS["Val"])


def guard_gfn(hole_info, return_type, var_types, param_args):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars = [v for v in keep_vars if v != "ghost_table"]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"), ["Start1", ["not", "Start1"]]],
		["Start1", "Bool", ["(Rel set.member)", "(Rel =)"]],
		mk_in_rule(depends),
		mk_eq_rule(depends),
		[*mk_tnt(("Set", TAS["Key"])),
   			[
				mk_nt(('Set', TAS['Key']), "Sub"),
				mk_select_idiom(TAS["Owner"]),
			]],
		[*mk_tnt(TAS["Val"]), 
   			[
				mk_nt(TAS['Val'], "Sub"),
				(TAS["Val"], None),
				mk_select_idiom(TAS["Table"]),
			]],
	]
	atom_except = [TAS["Val"], ("Set", TAS["Key"])]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	grammar += mk_atom_rules(depends, atom_except)
	return depends, grammar

def guard_gfn_inf(hole_info, return_type, var_types, param_args):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars = [v for v in keep_vars if v != "ghost_table"]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		["Start", "Bool", 
            [
				"(Rel set.member)", "(Rel =)",
				["not", "Start"],
				["or", "Start", "Start"],
				["and", "Start", "Start"],
            ]],
		mk_in_rule(depends),
		mk_eq_rule(depends),
		[*mk_tnt(("Set", TAS["Key"])),
   			[
				mk_nt(('Set', TAS['Key']), "Sub"),
				mk_select_idiom(TAS["Owner"]),
			]],
		[*mk_tnt(TAS["Val"]), 
   			[
				mk_nt(TAS['Val'], "Sub"),
				(TAS["Val"], None),
				mk_select_idiom(TAS["Table"]),
			]],
	]
	atom_except = [TAS["Val"], ("Set", TAS["Key"])]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	grammar += mk_atom_rules(depends, atom_except)
	return depends, grammar

def update_gfn(hole_info, return_type, var_types, param_args):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt(("Set", TAS["TMsg"]), "Start"), mk_set_idiom(TAS["TMsg"])],
		[*mk_tnt(("Set", TAS["Event"]), "Start"), mk_set_idiom(TAS["Event"])],
		[*mk_tnt(TAS["Owner"], "Start"), mk_store_idiom(TAS["Owner"])],
		[*mk_tnt(TAS["Table"], "Start"), mk_store_idiom(TAS["Table"])],
		#
		[*mk_tnt(("Set", TAS["Key"])),
			[
				mk_nt(("Set", TAS["Key"]), "Sub"),
				mk_select_idiom(TAS["Owner"]),
				*mk_set_idiom(TAS["Key"])]],
		[*mk_tnt(TAS["Val"]), 
   			[
				mk_nt(TAS['Val'], "Sub"),
				(TAS["Val"], None),
				mk_select_idiom(TAS["Table"]),
			]],
		["Int", "Int", [("Int", x) for x in [0,1]]],
	]
	#
	atom_except = [TAS["Val"], ("Set", TAS["Key"]), "Int"]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = [TAS["Table"], TAS["Owner"]]
	grammar += mk_atom_rules(depends, atom_except, atom_require)
	
	start_nt = mk_nt(return_type, "Start")
	starts = [r for r in grammar if r[0] == start_nt]
	if len(starts) != 1:
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != start_nt]
	grammar = [start] + rest
	return depends, grammar	

def update_gfn_inf(hole_info, return_type, var_types, param_args):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		# [*mk_tnt(("Set", TAS["TMsg"]), "Start"), mk_set_idiom(TAS["TMsg"])],
		# [*mk_tnt(("Set", TAS["Event"]), "Start"), mk_set_idiom(TAS["Event"])],
		mk_inf_set_idiom(("Set", TAS["TMsg"]), wrap="Start"),
		mk_inf_set_idiom(("Set", TAS["Event"]), wrap="Start"),
		[*mk_tnt(TAS["Owner"], "Start"), mk_store_idiom(TAS["Owner"])],
		[*mk_tnt(TAS["Table"], "Start"), mk_store_idiom(TAS["Table"])],
		#
		mk_inf_set_idiom(("Set", TAS["Key"]), wrap="Start"),
		[*mk_tnt(("Set", TAS["Key"])),
			[
				mk_nt(("Set", TAS["Key"]), "Start"),
				mk_nt(("Set", TAS["Key"]), "Sub"),
				mk_select_idiom(TAS["Owner"])]],
		[*mk_tnt(TAS["Val"]), 
   			[
				mk_nt(TAS['Val'], "Sub"),
				(TAS["Val"], None),
				mk_select_idiom(TAS["Table"]),
			]],
		["Int", "Int", [("Int", x) for x in [0,1]]],
	]
	#
	atom_except = [TAS["Val"], ("Set", TAS["Key"]), "Int"]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = [TAS["Table"], TAS["Owner"]]
	grammar += mk_atom_rules(depends, atom_except, atom_require)
	
	start_nt = mk_nt(return_type, "Start")
	starts = [r for r in grammar if r[0] == start_nt]
	if len(starts) != 1:
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != start_nt]
	grammar = [start] + rest
	return depends, grammar	