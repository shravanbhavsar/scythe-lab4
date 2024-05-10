from .mk_sketch import get_act_params, get_raw_act_name, load_sketch_meta, mk_holes, mk_init_act_params, mk_set

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'lock_serv'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

from .lock_serv_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"lock_msg" : TAS["Indicator"],
	"grant_msg" : TAS["Indicator"],
	"unlock_msg" : TAS["Indicator"],
	"holds_lock" : TAS["Indicator"],
	"server_holds_lock" : "Bool",
	"n" : TAS["Node"],
}

# set
FAIR_ACTIONS = {
	"RecvGrant",
	"RecvUnlock",
	"Unlock",
	"RecvLock",
	"SendLock",
}

CONST_NODES = ["n1", "n2", "n3"]

# dict arg_name -> list of possible values
PARAM_VALS = {
	"n" : CONST_NODES,
}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {

}

# list of constants (name, type)
const = [
    *[(n, TAS["Node"]) for n in CONST_NODES],
    ("Node", TAS["SetNode"]),
]

# list of assumptions (sexpr)
assumes = [
	["!=", *CONST_NODES],
	["=", "Node", mk_set(CONST_NODES)]
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]

from .mk_sketch import mk_trivial_grammar2 as gfn2

from .lock_serv_grams import guard_gfn_inf as guard_gfn
from .lock_serv_grams import update_gfn_inf as update_gfn

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