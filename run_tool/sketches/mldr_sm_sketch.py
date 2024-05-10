try:
	from .mk_sketch import load_sketch_meta, mk_holes 
	from .mk_sketch import mk_init_act_params, mk_set
	from .mk_sketch import mk_trivial_grammar2 as g2
	from .mk_sketch import get_act_params
except ImportError:
	from mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, mk_set
	from mk_sketch import mk_trivial_grammar2 as g2
	from mk_sketch import get_act_params

import itertools
from pprint import pprint
from pathlib import Path



PREFIX = 'mldr_sm'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
config2 = open(dir_path / f'{PREFIX}2.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .mldr_sm_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"currentTerm" : TAS["Terms"],
	"state" : TAS["Modes"],
	"configVersion" : TAS["ConfigVersions"],
	"configTerm" : TAS["ConfigTerms"],
	"config" : TAS["Configs"],
	"i" : TAS["Server"],
	"j" : TAS["Server"],
	"newConfig" : TAS["Config"],
	"voteQuorum" : TAS["SetServer"],
	"newTerm" : TAS["Term"],
	"newVersion" : TAS["ConfigVersion"],
	"Primary" : TAS["Mode"],
	"Secondary" : TAS["Mode"],
}

# set
FAIR_ACTIONS = {
	"Reconfig",
}

num_nodes = 3
CONST_SERVERS = [f"n{i+1}" for i in range(num_nodes)]
CONST_CONFIGS = [
    set(x) for x in itertools.chain.from_iterable([
        x for x in [
			itertools.combinations(CONST_SERVERS, i) 
			for i in range(len(CONST_SERVERS) + 1)]])]
SEXPR_CONFIGS = [mk_set(list(Q), TAS["Server"]) for Q in CONST_CONFIGS]

CONST_QUORUMS = [
    set(x) for x in itertools.chain.from_iterable([
        x for x in [
			itertools.combinations(CONST_SERVERS, i) 
			for i in range(len(CONST_SERVERS) + 1)]])
    if len(x) > len(CONST_SERVERS) // 2]
SEXPR_QUORUMS = [mk_set(list(Q)) for Q in CONST_QUORUMS]

CONST_TERMS = [("Int", x) for x in range(num_nodes+1)]
CONST_CONFIG_VERSIONS = [("Int", x) for x in range(1,num_nodes+1)]

# dict arg_name -> list of possible values
PARAM_VALS = {
	"i" : CONST_SERVERS,
	"j" : CONST_SERVERS,
	"newConfig" : SEXPR_CONFIGS,
	"voteQuorum" : SEXPR_QUORUMS,
	"newTerm" : CONST_TERMS,
	"newVersion" : CONST_CONFIG_VERSIONS,
}

# TODO: deprecate this
def mk_Quorums_expl(X, Q=None):
	if Q is None:
		Q = f"Q{abs(hash(frozenset(X)))}"
	return [
		"comprehension", Q, ["powerset", X], 
			[">", 
				["*", ["cardinality", Q], ("Int", 2)],
				["cardinality", X]]]

def mk_Quorums(X):
	return ["operator", "Quorums", X]

def mk_ConfigQuorumCheck(i):
	return [
		"exists", "Q", mk_Quorums_expl(["select", "config", i]), 
			["forall", "t", "Q",
				["and", 
	 				["=", 
	   					["select", "configTerm", "t"], 
						["select", "configTerm", i]],
					["=",
						["select", "configVersion", "t"],
						["select", "configVersion", i]]
				]
			]
		]

def mk_TermQuorumCheck(i, Q=None):
	Q = "Q"
	return [
		"exists", Q, mk_Quorums_expl(["select", "config", i]), 
			["forall", "t", Q,
				["=", 
					["select", "currentTerm", "t"], 
					["select", "currentTerm", "i"]
				]
			]
		]

def mk_QuorumsOverlap_expl(X, Y):
	return [
		"forall", "qx", mk_Quorums_expl(X, "QX"),
		["forall", "qy", mk_Quorums_expl(Y, "QY"),
			["not", ["=",
				(TAS["SetServer"], "emptyset"),
				["set.intersect", "qx", "qy"]]]]]

def mk_QuorumsOverlap(X, Y):
	return [
		"forall", "qx", mk_Quorums(X),
		["forall", "qy", mk_Quorums(Y),
			["not", ["=",
				(TAS["SetServer"], "emptyset"),
				["set.intersect", "qx", "qy"]]]]]

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {
	'__Reconfig(i, newConfig, newVersion)_g1__' : 
		# 'ConfigQuorumCheck(i)',
		mk_ConfigQuorumCheck("i"),
 	'__Reconfig(i, newConfig, newVersion)_g2__' : 
		# 'TermQuorumCheck(i)',
		mk_TermQuorumCheck("i"),
	'__Reconfig(i, newConfig, newVersion)_g3__' : 
		# 'QuorumsOverlap(config[i], newConfig)',
		mk_QuorumsOverlap(["select", "config", "i"], "newConfig"),
	'__Reconfig(i, newConfig, newVersion)_configTerm__' : 
		# '[configTerm EXCEPT ![i] = currentTerm[i]]',
		["store", "configTerm", "i", ["select", "currentTerm", "i"]],
	'__Reconfig(i, newConfig, newVersion)_g7__' :
		["=", 
   			["+", ("Int", 1), ["select", "configVersion", "i"]], 
			"newVersion"],
}

# list of constants (name, type)
const = [
	("Primary", TAS["Mode"]),
	("Secondary", TAS["Mode"]),
]
const += [(n, TAS["Server"]) for n in CONST_SERVERS]

# list of assumptions (sexpr)
assumes = [

]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]
act_params["BecomeLeader"] = ["i", "voteQuorum", "newTerm"]
act_params["UpdateTerms"] = ["i", "j", "newTerm"]
act_params["SendConfig"] = ["i", "j", "newTerm", "newVersion"]
act_params["Termination"] = []

# from .mldr_sm_grams import guard_gfn as guard_gfn
from .mldr_sm_grams import guard_gfn_cardinality as guard_gfn
from .mldr_sm_grams import update_gfn_inf as update_gfn

def gfn(hole_info, return_type, var_types, param_args, default):
	is_guard = hole_info["update_var"] is None
	if is_guard:
		return guard_gfn(hole_info, return_type, var_types, param_args, default)
	else:
		return update_gfn(
			hole_info, return_type, var_types, param_args, default)

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH, gfn
)
