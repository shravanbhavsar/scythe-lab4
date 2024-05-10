try:
	from .mk_sketch import load_sketch_meta, mk_holes 
	from .mk_sketch import mk_init_act_params, mk_set
	from .mk_sketch import mk_trivial_grammar2 as g2
except ImportError:
	from mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, mk_set
	from mk_sketch import mk_trivial_grammar2 as g2


import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'mldr'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
config2 = open(dir_path / f'{PREFIX}2.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .mldr_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"currentTerm" : TAS["Terms"],
	"state" : TAS["Modes"],
	"log" : TAS["Logs"],
	"immediatelyCommitted" : TAS["IC"],
	"configVersion" : TAS["ConfigVersions"],
	"configTerm" : TAS["ConfigTerms"],
	"config" : TAS["Configs"],
	"i" : TAS["Server"],
	"j" : TAS["Server"],
	"voteQuorum" : TAS["SetServer"],
	"newConfig" : TAS["Config"],
	"newVersion" : TAS["ConfigVersion"],
	"newTerm" : TAS["Term"],
	"Primary" : TAS["Mode"],
	"Secondary" : TAS["Mode"],
}

# set
FAIR_ACTIONS = {
	"Reconfig",
}

max_config_version = 3
max_term = 3
CONST_SERVERS = ["n1", "n2", "n3"]
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

# dict arg_name -> list of possible values
PARAM_VALS = {
	"i" : CONST_SERVERS,
	"j" : CONST_SERVERS,
	"newConfig" : SEXPR_CONFIGS,
	"newVersion" : [("Int", i) for i in range(1, max_config_version + 1)],
	"newTerm" : [("Int", i) for i in range(0, max_term + 1)],
	"voteQuorum" : SEXPR_QUORUMS,
}


def mk_Quorums(X):
	return ["operator", "Quorums", X]

def mk_ConfigQuorumCheck(i):
	return [
		"exists", "Q", mk_Quorums(["select", "config", i]), 
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
		"exists", Q, mk_Quorums(["select", "config", i]), 
			["forall", "t", Q,
				["=", 
					["select", "currentTerm", "t"], 
					["select", "currentTerm", "i"]
				]
			]
		]

def mk_QuorumsOverlap(X, Y):
	return [
		"forall", "qx", mk_Quorums(X),
		["forall", "qy", mk_Quorums(Y),
			["not", ["=",
				(TAS["SetServer"], "emptyset"),
				["set.intersect", "qx", "qy"]]]]]

def mk_iterated_and(*l):
	if len(l) == 0:
		raise ValueError("empty list")
	elif len(l) == 1:
		return l[0]
	else:
		return ["and", l[0], mk_iterated_and(*l[1:])]

def mk_GetTerm(xlog, idx):
	return ["ite", ["=", idx, ("Int", 0)], ("Int", 0), ["seq.at", xlog, idx]]

def mk_LogTerm(primary, idx):
	return mk_GetTerm(["select", "log", primary], idx)

def mk_IsCommitted(idx, primary):
	return mk_iterated_and(
		[">=", ["seq.len", ["select", "log", primary]], idx],
		["=", mk_LogTerm(primary, idx), ["select", "currentTerm", primary]],
		["exists", "quorum", mk_Quorums(["select", "config", primary]),
			["forall", "s", "quorum",
				["exists", "k", ["seq.domain", ["select", "log", "s"]],
					mk_iterated_and(
						["=", "k", idx],
						["=", 
	   						["seq.at", ["select", "log", "s"], "k"],
							["seq.at", ["select", "log", primary], "k"]],
						["=", 
	   						["select", "currentTerm", "s"], 
							["select", "currentTerm", primary]]
					)
				]
			]
		]
	)

def mk_OplogCommitment(s):
	return ["and",
		["or",
			["=", "immediatelyCommitted", (TAS["IC"], "emptyset")],
			["exists", "c", "immediatelyCommitted",
				["=", 
					["tuple.at", "c", ("Int", 2)],
					["select", "currentTerm", s]
				]
			]
   		],
		["forall", "c", "immediatelyCommitted",
			["=>",
				["=", 
	 				["tuple.at", "c", ("Int", 2)],
					["select", "currentTerm", s]
				],
				mk_IsCommitted(
						["tuple.at", "c", ("Int", 1)], 
						s
					)
			] 
		]
	]

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
	'__Reconfig(i, newConfig, newVersion)_g4__' : 
		# 'OplogCommitment(i)',
		mk_OplogCommitment("i"),
	'__Reconfig(i, newConfig, newVersion)_configTerm__' : 
		# '[configTerm EXCEPT ![i] = currentTerm[i]]',
		["store", "configTerm", "i", ["select", "currentTerm", "i"]],
	'__Reconfig(i, newConfig, newVersion)_g7__' :
		["=", 
   			["+", ("Int", 1), ["select", "configVersion", "i"]], 
			"newVersion"],
	'__Reconfig(i, newConfig, newVersion)_configVersion__' : 
		# '[configVersion EXCEPT ![i] = configVersion[i] + 1]',
		["store", "configVersion", "i", "newVersion"],
}

# list of constants (name, type)
const = [
	("Primary", TAS["Mode"]),
	("Secondary", TAS["Mode"]),
]
const += [(n, TAS["Server"]) for n in CONST_SERVERS]

# list of assumptions (sexpr)
assumes = []

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]
act_params["ClientRequest"] = ["i"]
act_params["GetEntries"] = ["i", "j"]
act_params["RollbackEntries"] = ["i", "j"]
act_params["CommitEntry"] = ["i", "voteQuorum"]
act_params["BecomeLeader"] = ["i", "voteQuorum", "newTerm"]
act_params["UpdateTerms"] = ["i", "j"]
act_params["SendConfig"] = ["i", "j"]
act_params["Termination"] = []

from .mldr_grams import guard_gfn_cardinality as guard_gfn
from .mldr_grams import update_gfn_inf as update_gfn

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
