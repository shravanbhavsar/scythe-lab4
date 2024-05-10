from pprint import pprint
from .mk_sketch import mk_trivial_grammar2 as g2
from .mk_sketch import get_act_params
from .grammar_helpers import mk_eq_rule, mk_in_rule, mk_inf_set_idiom, mk_inf_set_store_idiom, mk_nt, mk_atom_rules, mk_param_nt, mk_select_idiom, mk_store_idiom, mk_tnt

TAS : dict = {
    "Server" : ("Dom", "Server"),
    "Mode" : ("Dom", "Mode"),
    "LogLen" : "Int",
    "Term" : "Int",
    "ConfigVersion" : "Int",
}
TAS["SetServer"] = ("Set", TAS["Server"])
TAS["Config"] = TAS["SetServer"]
TAS["LocalLog"] = ("Seq", TAS["Term"])
TAS["IC"] = ("Set", ("Tuple", TAS["LogLen"], TAS["Term"])) 
#^ type of immediatelyCommitted
TAS["Logs"] = ("Array", TAS["Server"], TAS["LocalLog"]) # type of log
TAS["Terms"] = ("Array", TAS["Server"], TAS["Term"]) # type of currentTerm
TAS["Modes"] = ("Array", TAS["Server"], TAS["Mode"]) # type of state
TAS["Configs"] = ("Array", TAS["Server"], TAS["Config"]) # type of config
TAS["ConfigVersions"] = ("Array", TAS["Server"], TAS["ConfigVersion"]) 
#^ type of configVersion
TAS["ConfigTerms"] = ("Array", TAS["Server"], TAS["Term"]) # type of configTerm

def mk_guard_sub_grammar_alt(depends, cardinality_rules, *args):
	grammar = [
		[mk_param_nt("Start", *args), "Bool", 
			[
				mk_param_nt("Start1", *args), 
				["not", mk_param_nt("Start1", *args)]]],
		[mk_param_nt("Start1", *args), "Bool", 
			[mk_param_nt(nt, *args) for nt in [
				"(Rel =)", 
				"(Rel set.member)",
				"Bool",
			]] + [
				["<", mk_nt("Int", params=args), mk_nt("Int", params=args)],
				["<=", mk_nt("Int", params=args), mk_nt("Int", params=args)],
			] + [
				[op, 
	 				mk_param_nt("const_int", *args), 
					mk_param_nt("cardinality", *args)] 
					for op in ["=", "<", "<="]]],
		mk_in_rule(depends, params=args),
		mk_eq_rule(depends, params=args),
		[*mk_tnt(TAS["Mode"], params=args),
			[
				mk_nt(TAS["Mode"], "Sub", params=args),
				mk_select_idiom(TAS["Modes"], params=args),
			]
		],
		[*mk_tnt(TAS["Term"], params=args), 
			#also covers TAS["ConfigVersion"] since both de-alias to "Int"
			[
				mk_param_nt("const_int", *args),
				mk_nt(TAS["Term"], "Sub", params=args),
				mk_select_idiom(TAS["Terms"], params=args),
				mk_select_idiom(TAS["ConfigVersions"], params=args),
				# ["+", mk_nt(TAS["Term"], params=args), ("Int", 1)],
			] #+ cardinality_rules(args)
		],
		[*mk_tnt(TAS["Config"], params=args),
			[
				(TAS["Config"], "emptyset"),
				["set.intersect", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				["set.union", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				["set.minus", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				mk_nt(TAS["Config"], "Sub", params=args),
				mk_select_idiom(TAS["Configs"], params=args)
			] + list(args)
		],
		[mk_param_nt("const_int", *args), "Int", [("Int", 0), ("Int", 1)]],
		[mk_param_nt("cardinality", *args), "Int", cardinality_rules(args)]
	]
	atom_except = [TAS["Mode"], TAS["Term"], TAS["Config"]]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = [TAS["Mode"], TAS["Term"], TAS["Config"], "Bool"]
	grammar += mk_atom_rules(
		depends, atom_except=atom_except, atom_require=atom_require, 
		params=args)
	return grammar

def mk_guard_sub_grammar(depends, cardinality_rules, *args):
	grammar = [
		[mk_param_nt("Start", *args), "Bool", 
			[
				mk_param_nt("Start1", *args), 
				["not", mk_param_nt("Start1", *args)]]],
		[mk_param_nt("Start1", *args), "Bool", 
			[mk_param_nt(nt, *args) for nt in [
				"(Rel =)", 
				"(Rel set.member)",
				"Bool",
			]] + [
				["<", mk_nt("Int", params=args), mk_nt("Int", params=args)],
				["<=", mk_nt("Int", params=args), mk_nt("Int", params=args)],
			]
			],
		mk_in_rule(depends, params=args),
		mk_eq_rule(depends, params=args),
		[*mk_tnt(TAS["Mode"], params=args),
			[
				mk_nt(TAS["Mode"], "Sub", params=args),
				mk_select_idiom(TAS["Modes"], params=args),
			]
		],
		[*mk_tnt(TAS["Term"], params=args), 
			#also covers TAS["ConfigVersion"] since both de-alias to "Int"
			[
				("Int", 0),
				("Int", 1),
				mk_nt(TAS["Term"], "Sub", params=args),
				mk_select_idiom(TAS["Terms"], params=args),
				mk_select_idiom(TAS["ConfigVersions"], params=args),
				# ["+", mk_nt(TAS["Term"], params=args), ("Int", 1)],
			] + cardinality_rules(args)
		],
		[*mk_tnt(TAS["Config"], params=args),
			[
				(TAS["Config"], "emptyset"),
				["set.intersect", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				["set.union", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				["set.minus", 
					mk_nt(TAS["Config"], params=args),
					mk_nt(TAS["Config"], params=args)],
				mk_nt(TAS["Config"], "Sub", params=args),
				mk_select_idiom(TAS["Configs"], params=args)
			] + list(args)
		]
	]
	atom_except = [TAS["Mode"], TAS["Term"], TAS["Config"]]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = [TAS["Mode"], TAS["Term"], TAS["Config"], "Bool"]
	grammar += mk_atom_rules(
		depends, atom_except=atom_except, atom_require=atom_require, 
		params=args)
	return grammar

def guard_gfn_param(
		hole_info, return_type, var_types, param_args, default, sub_gfn):
	# We don't run experiments on these holes yet
	if hole_info["ufn"] in [
		"__Reconfig(i, newConfig, newVersion)_g1__",
		"__Reconfig(i, newConfig, newVersion)_g2__",
			]:
		return g2(hole_info, return_type, var_types, param_args, default)
	
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars = [v for v in keep_vars if v != "req_history"]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		["Start", "Bool",
   			[
				mk_param_nt("Start"),
				["forall", 
	 				"qx", 
	 				["operator", "Quorums", ["select", "config", "i"]],
					["forall", 
						"qy",
						["operator", "Quorums", "newConfig"],
						mk_param_nt("Start", "qx", "qy") 
					]
				]
			]
		],
	]
	grammar += sub_gfn(depends)
	grammar += sub_gfn(depends, "qx", "qy")
	return depends, grammar

def guard_gfn(hole_info, return_type, var_types, param_args, default):
	sub_gfn = lambda depends, *args: mk_guard_sub_grammar_alt(
		depends, lambda x: [], *args)
	return guard_gfn_param(
		hole_info, return_type, var_types, param_args, default, 
		sub_gfn)

def guard_gfn_cardinality(
		hole_info, return_type, var_types, param_args, default):
	card_fn = lambda args: [
		["cardinality", mk_nt(TAS["Config"], params=args)]]
	sub_gfn = lambda depends, *args: mk_guard_sub_grammar_alt(
		depends, card_fn, *args)
	return guard_gfn_param(
		hole_info, return_type, var_types, param_args, default, 
		sub_gfn)

def update_gfn_inf(hole_info, return_type, var_types, param_args, default):
	# return g2(hole_info, return_type, var_types, param_args, default)

	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt(TAS["Terms"], "Start"), 
			mk_store_idiom(TAS["Terms"])],
		*mk_inf_set_store_idiom(
            TAS["Configs"], wrap="Start"),
		mk_inf_set_idiom(TAS["IC"], wrap="Start"),
		[*mk_tnt(TAS["Modes"],"Start"),
			mk_store_idiom(TAS["Modes"])],
		[*mk_tnt(TAS["Logs"], "Start"),
			mk_store_idiom(TAS["Logs"])],
		[*mk_tnt("Int"), [
            mk_nt("Int", "Sub"),
        ]],
	]
	atom_except = ["Int"]
	atom_except = dict([(t, mk_nt(t, "Sub")) for t in atom_except])
	atom_require = ["Int"]
	grammar += mk_atom_rules(
		depends, atom_except=atom_except, atom_require=atom_require)
	
	start_nt = mk_nt(return_type, "Start")
	starts = [r for r in grammar if r[0] == start_nt]
	if len(starts) != 1:
		pprint(grammar)
		print(start_nt)
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != start_nt]
	grammar = [start] + rest
	return depends, grammar