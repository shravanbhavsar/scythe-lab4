from .mk_sketch import get_act_params
from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_nt, mk_select_idiom, mk_store_idiom, mk_tnt, mk_atom_rule, mk_tuple_rule, mk_union_rule, mk_ts_rec, mk_set_nt

TAS : dict = {
    "Pid" : ("Dom", "ProcSet"),
}
TAS["PS"] = ("Set", TAS["Pid"])
TAS["Fs"] = ("Array", TAS["Pid"], "Bool")
TAS["PC"] = ("Array", TAS["Pid"], "Int")

def guard_gfn(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"),
			[
                "Start1",
				["or", "Start1", "Start1"]]],
        ["Start1", "Bool", ["Start2", ["not", "Start2"]]],
        ["Start2", "Bool", ["Bool", "(Rel set.member)", "(Rel =)"]],
        mk_in_rule(depends),
        mk_eq_rule(depends),
		[*mk_tnt("Int"),
   			[
                mk_nt("Int", wrap="Sub"),
                *[("Int", i) for i in range(6)],
				["select", mk_nt(TAS["PC"]), "self"],
			]],
		[*mk_tnt("Bool"),
   			[
				mk_nt("Bool", wrap="Sub"),
                mk_select_idiom(TAS["Fs"]),
			]]
	]
	atom_except = ["Bool", "Int"]
	atom_except = {t : mk_nt(t, "Sub") for t in atom_except}
	grammar += mk_atom_rules(depends, atom_except)
     
	return depends, grammar

def guard_gfn_inf(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
		[*mk_tnt("Bool", wrap="Start"),
			[
				"Bool", "(Rel set.member)", "(Rel =)",
				["not", mk_nt("Bool", "Start")],
				["or", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
				["and", mk_nt("Bool", "Start"), mk_nt("Bool", "Start")],
        ]],
        mk_in_rule(depends),
        mk_eq_rule(depends),
		[*mk_tnt("Int"),
   			[
                mk_nt("Int", wrap="Sub"),
                *[("Int", i) for i in range(6)],
				["select", mk_nt(TAS["PC"]), "self"],
			]],
		[*mk_tnt("Bool"),
   			[
				mk_nt("Bool", wrap="Sub"),
                mk_select_idiom(TAS["Fs"], locals_nt="LocalPid"),
			]],
		["LocalPid", TAS["Pid"], ["self"]],
	]
	atom_except = ["Bool", "Int"]
	atom_except = {t : mk_nt(t, "Sub") for t in atom_except}
	grammar += mk_atom_rules(depends, atom_except)
     
	return depends, grammar

def update_gfn(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	grammar = [
        [*mk_tnt(TAS["PC"], wrap="Start"), 
        	[
                mk_nt(TAS["PC"]),
                ["store", mk_nt(TAS["PC"]), "self", mk_nt("Int")]
			]],
        [*mk_tnt(TAS["Fs"], wrap="Start"), 
			[
				mk_nt(TAS["Fs"]),
				["store", mk_nt(TAS["Fs"]), "self", mk_nt("Bool")]
			]],
        [*mk_tnt(TAS["Pid"], wrap="Start"), [mk_nt(TAS["Pid"])]],
		[*mk_tnt("Int"),
   			[
                mk_nt("Int", wrap="Sub"),
                *[("Int", i) for i in range(6)],
				["select", mk_nt(TAS["PC"]), "self"],
			]],
		[*mk_tnt("Bool"),
   			[
				mk_nt("Bool", wrap="Sub"),
                ("Bool", False),
                ("Bool", True),
                mk_select_idiom(TAS["Fs"]),
			]]
	]
	atom_except = ["Bool", "Int"]
	atom_except = {t : mk_nt(t, "Sub") for t in atom_except}
	grammar += mk_atom_rules(depends, atom_except)
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
        [*mk_tnt(TAS["PC"], wrap="Start"), 
        	[
                mk_nt(TAS["PC"]),
                ["store", mk_nt(TAS["PC"]), "self", mk_nt("Int")]
			]],
        [*mk_tnt(TAS["Fs"], wrap="Start"), 
			[
				mk_nt(TAS["Fs"]),
				["store", mk_nt(TAS["Fs"]), "self", mk_nt("Bool")]
			]],
        [*mk_tnt(TAS["Pid"], wrap="Start"), [mk_nt(TAS["Pid"])]],
		[*mk_tnt("Int"),
   			[
                mk_nt("Int", wrap="Sub"),
				*[("Int", i) for i in range(6)],
				["select", mk_nt(TAS["PC"]), "self"],
			]],
		[*mk_tnt("Bool"),
   			[
				mk_nt("Bool", wrap="Sub"),
                ("Bool", False),
                ("Bool", True),
				["not", mk_nt("Bool")],
				["or", mk_nt("Bool"), mk_nt("Bool")],
				["and", mk_nt("Bool"), mk_nt("Bool")],				
                mk_select_idiom(TAS["Fs"], locals_nt="LocalPid"),
			]],
		["LocalPid", TAS["Pid"], ["self"]],
	]
	atom_except = ["Bool", "Int"]
	atom_except = {t : mk_nt(t, "Sub") for t in atom_except}
	grammar += mk_atom_rules(depends, atom_except)
	start_nt = mk_nt(return_type, "Start")
	starts = [r for r in grammar if r[0] == start_nt]
	if len(starts) != 1:
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != start_nt]
	grammar = [start] + rest
	return depends, grammar	