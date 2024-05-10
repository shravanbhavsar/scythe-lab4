from .mk_sketch import get_act_params, get_raw_act_name, load_sketch_meta, mk_holes, mk_init_act_params, mk_set

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'peterson'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

CONST_PROCS = ["n1", "n2"]

from .peterson_grams import TAS

# dict var name -> type
VAR_TYPES = {
	"flag" : TAS["Fs"],
	"pc" : TAS["PC"],
	"turn" : TAS["Pid"],
	"other" : TAS["Pid"],
	"self" : TAS["Pid"],
}

# set
FAIR_ACTIONS = {
	"a3",
	"cs",
	"a1",
	"a4",
	"a5",
	"a2",
}

# dict arg_name -> list of possible values
PARAM_VALS = {
	"other" : CONST_PROCS,
	"self" : CONST_PROCS,
}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {
	"__a4(self, other)_g2__" : [
        "or",
        ["=", ["select", "flag", "other"], ("Bool", False)],
        ["=", "turn", "self"],
	]
}

# list of constants (name, type)
const = [("ProcSet", TAS["PS"])]
const += [(n, TAS["Pid"]) for n in CONST_PROCS]

# list of assumptions (sexpr)
assumes = [
	["!=", "n1", "n2"],
    ["=", 
     "ProcSet", mk_set(CONST_PROCS)],
]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]

from .mk_sketch import mk_trivial_grammar as gfn1

from .peterson_grams import guard_gfn_inf as guard_gfn
from .peterson_grams import update_gfn_inf as update_gfn

def gfn(hole_info, return_type, var_types, param_args, default):
    act_name = get_raw_act_name(hole_info)
    is_guard = hole_info["update_var"] is None
    # print(hole_info)
    if is_guard:
        return guard_gfn(hole_info, return_type, var_types, param_args, default)
    else:
        return update_gfn(
            hole_info, return_type, var_types, param_args, default)

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH, gfn
)
