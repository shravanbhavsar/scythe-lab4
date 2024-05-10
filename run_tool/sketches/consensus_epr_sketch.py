# from .grammar_helpers import mk_atom_rules, mk_eq_rule, mk_in_rule, mk_nt, mk_set_idiom, mk_set_store_idiom, mk_store_idiom, mk_subset_rule, mk_tnt
from .mk_sketch import get_act_params, load_sketch_meta, mk_holes, mk_init_act_params, mk_set

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'consensus_epr'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
config2 = open(dir_path / f'{PREFIX}2.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .consensus_epr_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"vote_request_msg" : TAS["SetMsg"],
	"voted" : TAS["Indicator"],
	"leader" : TAS["Indicator"],
	"vote_msg" : TAS["SetMsg"],
	"votes" : TAS["Votes"],
	"decided" : TAS["Decisions"],
	"src" : TAS["Node"],
	"sender" : TAS["Node"],
	"dst" : TAS["Node"],
	"Q" : TAS["SetNode"],
	"n" : TAS["Node"],
	"v" : TAS["Value"],
	# ghost variable:
	"req_history" : TAS["SetMsg"],
}

# set
FAIR_ACTIONS = {
	"IgnoreRequestVote",
	"RecvVote",
	"SendRequestVote",
	"Decide",
	"BecomeLeader",
	"SendVote",
}

CONST_NODES = ["n1", "n2", "n3"]
CONST_QUORUMS = [
    set(x) for x in itertools.chain.from_iterable([
        x for x in [
			itertools.combinations(CONST_NODES, i) 
			for i in range(len(CONST_NODES) + 1)]])
    if len(x) > len(CONST_NODES) // 2]
CONST_VALUES = ["v1", "v2"]
SEXPR_QUORUMS = [mk_set(list(Q)) for Q in CONST_QUORUMS]
# pprint(SEXPR_QUORUMS)
# assert(False)


# pprint(CONST_QUORUMS)
# assert(False)

# dict arg_name -> list of possible values
PARAM_VALS = {
	"src" : CONST_NODES,
	"sender" : CONST_NODES,
	"dst" : CONST_NODES,
	"Q" : SEXPR_QUORUMS,
	"n" : CONST_NODES,
	"v" : CONST_VALUES,
}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {
	'__SendVote(src, dst)_g0__' : 
		# '~voted[src]',
		["not", ["select", "voted", "src"]],
	"__RecvVote(n, sender)_votes__" : [
		"store", "votes", "n", 
			["set.union", ["select", "votes", "n"], ["set.singleton", "sender"]]
	],
	"__Decide(n, v)_g1__"  : [
		"=", ["select", "decided", "n"], (TAS["SetValue"], "emptyset"),
	],
	"__Decide(n, v)_decided__" : [
		"store", "decided", "n", 
			["set.union", 
				["select", "decided", "n"], ["set.singleton", "v"]]
	],
}

# list of constants (name, type)
const = [
	("Node", TAS["SetNode"]), 
	("Value", TAS["SetValue"]), 
	("Quorum", TAS["SetSetNode"])]
const += [(n, TAS["Node"]) for n in CONST_NODES]
const += [(v, TAS["Value"]) for v in CONST_VALUES]
# const += [(Q, TAS["SetNode"]) for Q in CONST_QUORUMS]

# list of assumptions (sexpr)
assumes = [
	["=", "Node", mk_set(CONST_NODES)],
	["=", "Value", mk_set(CONST_VALUES)],
	["=", "Quorum", mk_set(SEXPR_QUORUMS)],
	["!=", *CONST_NODES],
	["!=", *CONST_VALUES],
]
# pprint(assumes[2])
# assert(False)

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]
act_params["SendRequestVote"] = ["src", "dst"]

from .mk_sketch import mk_trivial_grammar as gfn1
from .consensus_epr_grams import guard_gfn_inf as guard_gfn
from .consensus_epr_grams import update_gfn_inf as update_gfn

def gfn(hole_info, return_type, var_types, param_args, default):
	is_guard = hole_info["update_var"] is None
	if is_guard:
		return guard_gfn(hole_info, return_type, var_types, param_args, default)
	else:
		return update_gfn(hole_info, return_type, var_types, param_args, default)

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH, gfn
)
