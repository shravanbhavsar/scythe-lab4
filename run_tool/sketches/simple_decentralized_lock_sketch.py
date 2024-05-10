try:
	from .mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, get_raw_act_name
except:
	from mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params, get_raw_act_name

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'simple_decentralized_lock'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .simple_decentralized_lock_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"message" : TAS["SetMessage"],
	# "has_lock" : TAS["SetNode"],
	"has_lock" : TAS["Indicator"],
	"dst" : TAS["Node"],
	"src" : TAS["Node"],
}

# set
FAIR_ACTIONS = {
	"Recv",
	"Send",
}

# dict arg_name -> list of possible values
PARAM_VALS = {
	"dst" : ["n1", "n2", "n3"],
	"src" : ["n1", "n2", "n3"],
}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {
	# "__Send(src, dst)_message__" : [
    #     "set.union", "message", ["set.singleton", ["tuple", "src", "dst"]],
	# ],
    # "__Recv(src, dst)_g0__": [
    #     "set.member", ["tuple", "src", "dst"], "message"
	# ],
    # "__Recv(src, dst)_message__" : [
    #     "set.minus", "message", ["set.singleton", ["tuple", "src", "dst"],]
	# ],
}

# list of constants (name, type)
const = [
	("Node", TAS["SetNode"]), 
	("n1", TAS["Node"]), ("n2", TAS["Node"]), ("n3", TAS["Node"])]

# list of assumptions (sexpr)
assumes = [
	["=", "Node", 
  		["set.union", 
	 		["set.union", 
	 			["set.singleton", "n1"], 
				["set.singleton", "n2"]], 
			["set.singleton", "n3"]]],
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]


# gfn = None
from .mk_sketch import mk_trivial_grammar as gfn1

from .simple_decentralized_lock_grams import guard_gfn_inf as guard_gfn
from .simple_decentralized_lock_grams import update_gfn as update_gfn


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