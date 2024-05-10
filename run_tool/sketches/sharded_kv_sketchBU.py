try:
	from .mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params,  get_act_params, get_raw_act_name
except:
	from mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params,  get_act_params, get_raw_act_name

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'sharded_kv'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

# dict var name -> type
VAR_TYPES = {
	"table" : ("Array", ("Tuple", "Int", "Int"), "Int"),
	"owner" : ("Array", "Int", ("Set", "Int")),
	"transfer_msg" : ("Set", ("Tuple", "Int", "Int", "Int")),
	"v" : "Int",
	"n_new" : "Int",
	"k" : "Int",
	"n_old" : "Int",
	"n" : "Int",
}

# set
FAIR_ACTIONS = {
	"Put",
	"Reshard",
	"RecvTransferMsg",
}

N = 3
# dict arg_name -> list of possible values
PARAM_VALS = {
	"v" : [f"v{i}" for i in range(1,N+1)],
	"n_new" : [f"n{i}" for i in range(1,N+1)],
	"k" : [f"k{i}" for i in range(1,N+1)],
	"n_old" : [f"n{i}" for i in range(1,N+1)],
	"n" : [f"n{i}" for i in range(1,N+1)],
}

def mk_store(table, k, v):
	return ["store", table, k, v]

def mk_double_store(table, k1, k2, v):
	# a2 = ["select", "table", k1]
	# return mk_store(table, k1, mk_store(a2, k2, v))
	return mk_store(table, ["tuple", k1, k2], v)

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {
	# '__Reshard(k,v,n_old,n_new)_table__' : (
    #     mk_double_store("table", "n_old", "k", ("Int", None))),
	# '__Reshard(k,v,n_old,n_new)_owner__' : (
	# 	mk_store(
	# 		"owner", "n_old", 
	# 		["set.minus", 
	# 			["select", "owner", "n_old"],
	# 			["set.singleton", "k"]])
	# ),
	# '__Reshard(k,v,n_old,n_new)_transfer_msg__' : (
	# 	["set.union", 
   	# 		"transfer_msg", 
	# 		["set.singleton", ["tuple", "n_new", "k", "v"]]]
	# ),
	# '__RecvTransferMsg(n, k, v)_g0__' : (
	# 	["set.member", ["tuple", "n", "k", "v"], "transfer_msg"]
	# ),
	# '__RecvTransferMsg(n, k, v)_transfer_msg__' : (
	# 	["set.minus", 
   	# 		"transfer_msg", 
	# 		["set.singleton", ["tuple", "n", "k", "v"]]]
	# ),
	# '__RecvTransferMsg(n, k, v)_table__' : (
	# 	mk_double_store("table", "n", "k", "v")
	# ),
	# '__RecvTransferMsg(n, k, v)_owner__' : (
	# 	mk_store(
	# 		"owner", "n", 
	# 	   	["set.union", ["select", "owner", "n"], ["set.singleton", "k"]])
	# ),
	# '__Put(n, k, v)_g0__' : (
	# 	["set.member", "k", ["select", "owner", "n"]]
	# ),
	# '__Put(n, k, v)_table__' : (
	# 	mk_double_store("table", "n", "k", "v")
	# ),
}

# list of constants (name, type)
const = [
	("Key", ("Set", "Int")),
	("Value", ("Set", "Int")),
	("Node", ("Set", "Int")),
	("Nil", "Int"),
	("n1", "Int"),
	("n2", "Int"),
	("n3", "Int"),
	("k1", "Int"),
	("k2", "Int"),
	("k3", "Int"),
	("v1", "Int"),
	("v2", "Int"),
	("v3", "Int"),
]

def mk_set(lst):
	if len(lst) == 0:
		raise ValueError("Empty set")
	elif len(lst) == 1:
		return ["set.singleton", lst[0]]
	else:
		return ["set.union", lst[0], mk_set(lst[1:])]

# list of assumptions (sexpr)
assumes = [
	["!=", "n1", "n2", "n3"],
	["!=", "k1", "k2", "k3"],
	["!=", "v1", "v2", "v3", "Nil"],
	["=", "Key", mk_set(["k1", "k2", "k3"])],
	["=", "Value", mk_set(["v1", "v2", "v3"])],
	["=", "Node", mk_set(["n1", "n2", "n3"])],
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]

# from .mk_sketch import mk_trivial_grammar2 as gfn


def mk_nt(t):
    if isinstance(t, tuple):
        return f"({t[0]} {' '.join([mk_nt(x) for x in t[1:]])})"
    return t

def guard_gfn(hole_info, return_type, var_types, param_args, default):
	keep_vars = [v for v in var_types.keys() if v not in param_args]
	keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	Keys = ["k"]
	Nodes = ["n", "n_new", "n_old"]
	Vals = ["v"]
	nts = ["Val", "Key", "Node", "TKey", "TMsg", "(Set Key)", "(Set TMsg)"]
	grammar = [
		["Start", "Bool",
   			[
				"Start1",
				["not", "Start1"],
			]],
		["Start1", "Bool",
   			[
				"Membership",
				"Equality",
			]],
		["Membership", "Bool",
   			[
				["set.member", "Key", "(Set Key)"],
				["set.member", "TMsg", "(Set TMsg)"],
			]],
		["Equality", "Bool",
   			[
				["=", nt, nt] for nt in nts
			]],
		["(Set Key)", ("Set", "Int"),
   			[
				["select", "(Array Int (Set Int))", "Node"],
			]],
		["(Array Int (Set Int))", ("Array", "Int", ("Set", "Int")),
   			[
				   k for k,v in depends
				   if v == ("Array", "Int", ("Set", "Int"))
			]],
		["TKey", ("Tuple", "Int", "Int"), [["tuple", "Node", "Key"]]],
		["(Set TMsg)", ("Set", ("Tuple", "Int", "Int", "Int")),
			[
				k for k,v in depends 
				if v == ("Set", ("Tuple", "Int", "Int", "Int"))
			]
		],
		[
			"(Array (Tuple Int Int) Int)", 
			("Array", ("Tuple", "Int", "Int"), "Int"), 
   			[
				   k for k,v in depends
				   if v == ("Array", ("Tuple", "Int", "Int"), "Int")
			]],
		["TMsg", ("Tuple", "Int", "Int", "Int"), 
			[
				["tuple", "Node", "Key", "Val"],
			]],
		["Key", "Int", [k for k in Keys if k in keep_vars]],
		["Node", "Int", [k for k in Nodes if k in keep_vars]],
		["Val", "Int", 
   			([k for k in Vals if k in keep_vars]
	   		+ [("Int", None)]
	   		+ [["select", "(Array (Tuple Int Int) Int)", "TKey"]])],
	]
	return depends, grammar

def update_gfn(hole_info, return_type, var_types, param_args, default):
	uv = hole_info["update_var"]
	keep_vars = [uv] + get_act_params(hole_info)
	depends = [(k,v) for k,v in var_types.items() if k in keep_vars]
	Keys = ["k"]
	Nodes = ["n", "n_new", "n_old"]
	Vals = ["v"]
	grammar = [
		["(Set (Tuple Int Int Int))", ("Set", ("Tuple", "Int", "Int", "Int")),
			[
				"(Atom (Set (Tuple Int Int Int)))",
				[
					"set.union", 
					"(Atom (Set (Tuple Int Int Int)))", 
					["set.singleton", "TMsg"]
				],
				[
					"set.minus", 
					"(Atom (Set (Tuple Int Int Int)))", 
					["set.singleton", "TMsg"]
				],
			]],
		["(Array Int (Set Int))", ("Array", "Int", ("Set", "Int")),
			[
				"(Atom (Array Int (Set Int)))",
				[
					"store", 
					"(Atom (Array Int (Set Int)))", 
					"Node", 
					"(Set Int)"],
			]],
		[
			"(Array (Tuple Int Int) Int)", 
			("Array", ("Tuple", "Int", "Int"), "Int"),
			[
				"(Atom (Array (Tuple Int Int) Int))",
				[
					"store", 
					"(Atom (Array (Tuple Int Int) Int))", 
					"TKey", 
					"Val"
				],
			]],
		# 
		["(Set Int)", ("Set", "Int"),
			[
				"(Set Key)",
				[
					"set.union", 
					"(Set Key)", 
					["set.singleton", "Key"]
				],
				[
					"set.minus", 
					"(Set Key)", 
					["set.singleton", "Key"]
				],
			]],
		["(Atom (Set (Tuple Int Int Int)))", ("Set", ("Tuple", "Int", "Int", "Int")),
			[
				k for k,v in depends 
				if v == ("Set", ("Tuple", "Int", "Int", "Int"))
			]
		],
		["(Atom (Array Int (Set Int)))", ("Array", "Int", ("Set", "Int")),
   			[
				   k for k,v in depends
				   if v == ("Array", "Int", ("Set", "Int"))
			]],
		[
			"(Atom (Array (Tuple Int Int) Int))", 
			("Array", ("Tuple", "Int", "Int"), "Int"), 
   			[
				   k for k,v in depends
				   if v == ("Array", ("Tuple", "Int", "Int"), "Int")
			]],
		# 
		["(Set Key)", ("Set", "Int"),
   			[
				["select", "(Atom (Array Int (Set Int)))", "Node"],
			]],
		["TKey", ("Tuple", "Int", "Int"), [["tuple", "Node", "Key"]]],
		["TMsg", ("Tuple", "Int", "Int", "Int"), 
			[
				["tuple", "Node", "Key", "Val"],
			]],
		["Key", "Int", [k for k in Keys if k in keep_vars]],
		["Node", "Int", [k for k in Nodes if k in keep_vars]],
		["Val", "Int", 
   			([k for k in Vals if k in keep_vars]
	   		+ [("Int", None)]
	   		+ [["select", "(Atom (Array (Tuple Int Int) Int))", "TKey"]])]
	]
	
	starts = [r for r in grammar if r[0] == mk_nt(return_type)]
	if len(starts) != 1:
		raise ValueError("Expected exactly one return type. Got: ", starts)
	start = starts[0]
	rest = [r for r in grammar if r[0] != mk_nt(return_type)]
	grammar = [start] + rest
	return depends, grammar	

def gfn(hole_info, return_type, var_types, param_args, default):
	act_name = get_raw_act_name(hole_info)
	is_guard = hole_info["update_var"] is None
	if is_guard:
		return guard_gfn(hole_info, return_type, var_types, param_args, default)
	else:
		return update_gfn(
			hole_info, return_type, var_types, param_args, default)




holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH, gfn
)

# pprint(holes)