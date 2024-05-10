from .mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, get_raw_act_name, get_act_params, mk_set

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'sharded_kv'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .sharded_kv_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"table" : TAS["Table"],
	"owner" : TAS["Owner"],
	"transfer_msg" : ("Set", TAS["TMsg"]),
	"event_queue" : ("Set", TAS["Event"]),
	# 
	"v" : TAS["Val"],
	"k" : TAS["Key"],
	"n_old" : TAS["Node"],
	"n_new" : TAS["Node"],
	"n" : TAS["Node"],
	# 
	"GIVE" : "Int",
	"PUT" : "Int",
	#
	"ghost_table" : TAS["GTable"],
}

# set
FAIR_ACTIONS = {
	"RecvTransferMsg",
	"Reshard",
	"Put",
    "SchedulePut",
    "ScheduleGive",
}

CONST_NODES = ["n1", "n2", "n3"]
CONST_VALUES = ["v1", "v2"]
CONST_KEYS = ["k1", "k2"]

# dict arg_name -> list of possible values
PARAM_VALS = {
	"k" : CONST_KEYS,
	"v" : CONST_VALUES,
	"n_new" : CONST_NODES,
	"n_old" : CONST_NODES,
	"n" : CONST_NODES,
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
	'__Reshard(k,v,n_old,n_new)_table__' : (
        mk_double_store("table", "n_old", "k", (TAS["Val"], None))),
	'__Reshard(k,v,n_old,n_new)_owner__' : (
		mk_store(
			"owner", "n_old", 
			["set.minus", 
				["select", "owner", "n_old"],
				["set.singleton", "k"]])
	),
	'__RecvTransferMsg(n, k, v)_owner__' : (
		mk_store(
			"owner", "n", 
		   	["set.union", ["select", "owner", "n"], ["set.singleton", "k"]])
	),
	'__Put(n, k, v)_g2__' : (
		["set.member", "k", ["select", "owner", "n"]]
	),
}


# list of constants (name, type)
const = [
	("Key", ("Set", TAS["Key"])),
	("Value", ("Set", TAS["Val"])),
	("Node", ("Set", TAS["Node"])),
	("Nil", TAS["Val"]),
	("GIVE", "Int"),
	("PUT", "Int"),
]
const += [(k, TAS["Key"]) for k in CONST_KEYS]
const += [(v, TAS["Val"]) for v in CONST_VALUES]
const += [(n, TAS["Node"]) for n in CONST_NODES]


# list of assumptions (sexpr)
assumes = [
	["!=", *[n for n in CONST_NODES]],
	["!=", *[k for k in CONST_KEYS]],
	["!=", "Nil", *[v for v in CONST_VALUES]],
	["=", "Key", mk_set(CONST_KEYS)],
	["=", "Value", mk_set(CONST_VALUES)],
	["=", "Node", mk_set(CONST_NODES)],
	["=", "GIVE", "1"],
	["=", "PUT", "0"],
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]
act_params["SchedulePut"] = ["k", "v"]
act_params["ScheduleGive"] = ["k", "n_old", "n_new"]

# from .mk_sketch import mk_trivial_grammar2

from .sharded_kv_grams import guard_gfn_inf as guard_gfn
from .sharded_kv_grams import update_gfn_inf as update_gfn

def gfn(hole_info, return_type, var_types, param_args, default):
	is_guard = hole_info["update_var"] is None
	if is_guard:
		return guard_gfn(hole_info, return_type, var_types, param_args)
	else:
		return update_gfn(
			hole_info, return_type, var_types, param_args)

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH,
	gfn=gfn
)

# pprint(holes)
# assert(False)