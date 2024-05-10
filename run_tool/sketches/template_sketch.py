from .mk_sketch import load_sketch_meta, mk_holes, mk_init_act_params

import itertools
from pprint import pprint
from pathlib import Path

PREFIX = 'PROTOCOLNAME'
dir_path = Path(__file__).resolve().parent
sketch = open(dir_path / f'{PREFIX}_sketch.tla', "r").read()
config = open(dir_path / f'{PREFIX}.cfg', "r").read()
SKETCH_META = load_sketch_meta(dir_path / PREFIX)

# dict var name -> type
VAR_TYPES = {}

# set
FAIR_ACTIONS = {}

# dict arg_name -> list of possible values
PARAM_VALS = {}

# Some ground truths are not handled by the parser, so we will need to
# manually write conversion to sexpr for them.
# dict ufn -> sexpr
MANUAL_GROUND_TRUTH = {

}

# list of constants (name, type)
const = []

# list of assumptions (sexpr)
assumes = [

]

# try our best to extract the action parameters from the meta file
act_params = mk_init_act_params(SKETCH_META)
# example of action that needs to be handled manually because is was skipped or
# the sketch generator or because it occurred outside <action>...</action>
# act_params['<action name>'] = ['<param1>', '<param2>', ...]

holes = mk_holes(
    SKETCH_META, FAIR_ACTIONS, VAR_TYPES, PARAM_VALS, MANUAL_GROUND_TRUTH
)
