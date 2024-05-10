'''This module serves to take a ground truth .tla file and turn it into a sketch
file.
'''
import itertools
import json
import os

from pprint import pprint


def mk_set(lst, t=None):
    '''t, if provided, is the type of the set elements.
    '''
    if len(lst) == 0:
        if t is None:
            raise ValueError("Empty set w/o supplied type")
        return (("Set", t), "emptyset")
    elif len(lst) == 1:
        return ["set.singleton", lst[0]]
    else:
        return ["set.union", ["set.singleton", lst[0]], mk_set(lst[1:])]

def get_action_group(lines):
    '''
    '''

    olines = list(lines)

    # find the index of the line containing <actions>
    actions_index = None
    for i, line in enumerate(lines):
        if '<actions>' in line:
            actions_index = i
            break
    # find the index of the line containing </actions>
    end_actions_index = None
    for i, line in enumerate(lines):
        if '</actions>' in line:
            end_actions_index = i
            break

    if actions_index is None:
        raise ValueError('The .tla file does not contain an <actions> tag')
    if end_actions_index is None:
        raise ValueError('The .tla file does not contain an </actions> tag')

    # Slice the lines to get the actions
    prelines = "".join(olines[:actions_index])
    lines = olines[actions_index+1:end_actions_index]
    postlines = "".join(olines[end_actions_index+1:])
    return prelines, lines, postlines

def get_action_headers(lines):
    '''
    '''

    # Action names occur in lines without whitespace at the beginning.
    action_headers = [
        line for line in lines 
        if len(line.strip()) > 0 and line.strip()[0] == line[0]]
    # Action names occur in lines with "==" in them.
    for name in action_headers:
        if '==' not in name:
            raise ValueError(f'The action name {name} does not contain "=="')
    return action_headers

def get_action_blocks(lines, action_headers):
    '''
    '''

    # partition lines into lists of lines occuring between action names
    action_blocks = []
    for line in lines:
        if line in action_headers:
            action_blocks.append([])
            # continue
        if line.strip() == '':
            continue
        action_blocks[-1].append(line)
    return action_blocks

def process_clause(clause, action_name, idx):
    delim = "' ="
    if "UNCHANGED" in clause:
        # clause = clause.replace(">>", "")
        # vs = clause.split("<<")[1].split(",")
        # vs = [v.strip() for v in vs]
        # clauses = [f"{v}' = {v}" for v in vs]
        # clausess = [process_clause(c, action_name, idx) for c in clauses]
        # # clausess is a list of lists. combine them using itertools chain
        # return list(itertools.chain.from_iterable(clausess))
        return [(clause, {"gt" : clause})]
    elif delim in clause:
        clause_header = clause.split(delim)[0]
        ufn = f"__{action_name}_{clause_header}__"
        gt = clause.split(delim)[1].strip()
        clause_body = f"{ufn} \\* gt: {gt}"
        new_clause = f"{clause_header}' = {clause_body}"
    else:
        ufn = f"__{action_name}_g{idx}__"
        gt = clause
        clause_header = None
        new_clause = f"{ufn} \\* gt: {gt}"
    info = {
        "action_name": action_name,
        "update_var": clause_header,
        "ufn": ufn,
        "gt": gt,
    }
    res = (new_clause, info)
    return [res]

def process_action_block(action_block):
    '''
    '''

    action_name = action_block[0].split('==')[0].strip()
    action_block = action_block[1:]
    prefix = "    /\\"
    if any(not line.startswith(prefix) for line in action_block):
        print("Skipping action irregular clause structure", action_name)
        return action_block, None
    action_block = [line.replace(prefix, "") for line in action_block]
    action_block = [line.strip() for line in action_block]
    info = [
        process_clause(line, action_name, i) 
        for i, line in enumerate(action_block)]
    info = list(itertools.chain.from_iterable(info))
    # pprint(info)
    action_block = [i[0] for i in info]
    info = [i[1] for i in info]
    action_block = [f"    /\\ {line}" for line in action_block]
    action_block = [f"{action_name} =="] + action_block + ["\n"]
    return action_block, info

def process_tla(tla_file):
    '''
    '''

    with open(tla_file, 'r') as f:
        lines = f.readlines()

    vars = [line for line in lines if "vars == <<" in line]
    if len(vars) == 0:
        raise ValueError(
            'The .tla file does not contain a vars == <<...>> line')
    vars = vars[0]
    if ">>" not in vars:
        raise ValueError("Ensure vars == <<...>> is on one line.")
    vars = vars.replace(">>", "").split("<<")[1].split(",")
    vars = [v.strip() for v in vars]

    prelines, lines, postlines = get_action_group(lines)
    lines = [line for line in lines if line.strip()[:2] != "\\*"]
    action_headers = get_action_headers(lines)
    action_blocks = get_action_blocks(lines, action_headers)
    action_blocks_infos = [process_action_block(ab) for ab in action_blocks]
    actions, infos = zip(*action_blocks_infos)
    info = list(
        itertools.chain.from_iterable(
            [info for info in infos if info is not None]))
    actions = "\n".join(list(itertools.chain.from_iterable(actions)))
    res = "\n".join([prelines, actions, postlines])
    return res, info, vars

def mk_and_write_sketch(fname_prefix):
    tla_file = f'{fname_prefix}.tla'
    tla_sketch_file = f'{fname_prefix}_sketch.tla'
    tla_sketch, info, vars = process_tla(tla_file)
    with open(tla_sketch_file, 'w') as f:
        print(f'Creating {tla_sketch_file}')
        f.write(tla_sketch)
    with open(f'{fname_prefix}_meta.json', 'w') as f:
        print(f'Creating {fname_prefix}_meta.json')
        json.dump(info, f, indent=2)
    with open('template_sketch.py', 'r') as f:
        template = f.read()

    template = template.replace('PROTOCOLNAME', fname_prefix)
    

    raw_actions = {
        get_raw_act_name(act) for act in info if "action_name" in act}
    fair_actions_str = "\n".join([f'\t"{a}",' for a in raw_actions])
    fair_actions_str = f'FAIR_ACTIONS = {{\n{fair_actions_str}\n}}'
    template = template.replace('FAIR_ACTIONS = {}', fair_actions_str)

    param_vars = [
        get_act_params(act) for act in info if "action_name" in act]
    param_vars = set(itertools.chain.from_iterable(param_vars))
    param_vars = [p.strip() for p in param_vars if p.strip() != ""]
    param_vals_str = "\n".join([f'\t"{p}" : [],' for p in param_vars])
    param_vals_str = f'PARAM_VALS = {{\n{param_vals_str}\n}}'
    template = template.replace('PARAM_VALS = {}', param_vals_str)

    var_types_str = "\n".join([f"\t\"{v}\" : \"\"," for v in vars+param_vars])
    var_types_str = f'VAR_TYPES = {{\n{var_types_str}\n}}'
    template = template.replace('VAR_TYPES = {}', var_types_str)

    if not os.path.exists(f'{fname_prefix}_sketch.py'):
        print(
            f'Creating {fname_prefix}_sketch.py. Delete this to regenerate.' 
            ' You must manually fill in the VAR_TYPES, FAIR_ACTIONS, etc.')
        with open(f'{fname_prefix}_sketch.py', 'w') as f:
            f.write(template)

def load_sketch_meta(fname_prefix):
    with open(f'{fname_prefix}_meta.json', 'r') as f:
        meta = json.load(f)
    return meta

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # 

def mild_ground_truth_parsing(
        hole_info, var_types, param_args, default, ground_truth=None):

    if ground_truth is None:
        ground_truth = hole_info["gt"]

    def handle_in_operator(operator):
        left, right = ground_truth.split(operator)
        left = left.strip()
        right = right.strip()
        if left.startswith("<<") and left.endswith(">>"):
            left = handle_tuple_operator(left) 
        elif left not in var_types.keys():
            raise_not_implemented_error_left_side(operator, left)
        if " " in right:
            raise_not_implemented_error_right_side(operator, right)
        right = mild_ground_truth_parsing(
            hole_info, var_types, param_args, default, ground_truth=right)
        # elif right not in var_types.keys():
        #     raise_not_implemented_error_right_side(operator, right)
        if operator == "\\in":
            return ["set.member", left, right]
        elif operator == "\\notin":
            return ["not", ["set.member", left, right]]
        elif operator == "\\subseteq":
            return ["set.subset", left, right]
        else:
            raise ValueError(f"Unexpected 'in' operator: {operator}")

    def handle_set_operator(operator):
        left, right = ground_truth.split(operator)
        left = left.strip()
        right = right.strip()
        if left not in list(var_types.keys()):
            pprint(list(var_types.keys()))
            x = list(var_types.keys())[0]
            print(left, x, x == left, type(left), type(x))
            raise_not_implemented_error_left_side(operator, left)
        if right.startswith("{<<"):
            right = right[1:-1]
            if "{" in right or "}" in right:
                raise_not_implemented_error_right_side(operator, right)
            right = handle_tuple_operator(right)
            right = ["set.singleton", right]
        elif right in [f"{{{x}}}" for x in param_args]:
            right = [x for x in param_args if f"{{{x}}}" == right][0]
            right = ["set.singleton", right]
        elif right not in (
                list(var_types.keys())):
            raise_not_implemented_error_right_side(operator, right)
        if operator == "\\":
            return ["set.minus", left, right]
        elif operator == "\\cup":
            return ["set.union", left, right]
        elif operator == "\\cap":
            return ["set.intersect", left, right]
        else:
            raise ValueError(f"Unexpected set operator: {operator}")

    def handle_other_cases(operator):
        if operator in var_types.keys():
            return operator
        elif operator == "TRUE":
            return ("Bool", True)
        elif operator == "FALSE":
            return ("Bool", False)
        elif operator.isnumeric():
            return ("Int", int(operator))
        else:
            raise_not_implemented_error(operator)

    def handle_eq_operator(operator):
        x = ground_truth.split(operator)
        if len(x) != 2:
            raise_not_implemented_error(operator)
        left, right = x
        left = left.strip()
        right = right.strip()
        if " " in left:
            raise_not_implemented_error_left_side(operator, left)
        if " " in right:
            raise_not_implemented_error_right_side(operator, right)
        left = mild_ground_truth_parsing(
            hole_info, var_types, param_args, default, ground_truth=left)
        right = mild_ground_truth_parsing(
            hole_info, var_types, param_args, default, ground_truth=right)
        if operator == "=":
            return ["=", left, right]
        elif operator == "#":
            return ["not", ["=", left, right]]
        else:
            raise_not_implemented_error(operator)

    def handle_tuple_operator(i):
        i = i.replace(">>", "").replace("<<", "")
        i = i.split(",")
        i = [x.strip() for x in i]
        i = [mild_ground_truth_parsing(
            hole_info, var_types, param_args, default, ground_truth=x) for x in i]
        return ["tuple"] + i
        
    def handle_array_operator():
        if ground_truth is None or  len(ground_truth) == 0:
            raise_not_implemented_error("vacuous array operator")
        elif ground_truth[0] == "[":
            x = ground_truth.replace("]", "").replace("[", "").replace("!", "")
            x = x.split("EXCEPT")
            v = x[0].strip()
            x = x[1].split("=")
            i = x[0].strip()
            val = x[1].strip()
            if v not in var_types.keys():
                raise_not_implemented_error_left_side("array_store", v)
            if i.startswith("<<") and i.endswith(">>"):
                i = handle_tuple_operator(i)
            elif i not in var_types.keys():
                raise_not_implemented_error_left_side("array_store", i)
            if " " in val:
                raise_not_implemented_error_right_side("array_store", val)
            val = mild_ground_truth_parsing(
                hole_info, var_types, param_args, default, ground_truth=val)
            return ["store", v, i, val]
        else:
            x = ground_truth.replace("]", "").split("[")
            v = x[0].strip()
            idxs = [x.strip() for x in x[1:]]
            # assert(len(x) == 2)
            if v not in var_types.keys():
                raise_not_implemented_error_left_side("array_select", v)
            res = v
            for i in idxs:
                if i in var_types.keys():
                    pass
                elif i.startswith("<<") and i.endswith(">>"):
                    i = handle_tuple_operator(i) 
                else:
                    raise_not_implemented_error_right_side("array_select", i)
                res = ["select", res, i]
            return res

    def raise_not_implemented_error_left_side(operator, side):
        pprint(hole_info)
        raise NotImplementedError(
            f"left side of {operator} not in VAR_TYPES: {side}."
            "You will need to manually write the grammar for this.")

    def raise_not_implemented_error_right_side(operator, side):
        pprint(hole_info)
        raise NotImplementedError(
            f"right side of {operator} not in VAR_TYPES: {side}."
            "You will need to manually write the grammar for this.")

    def raise_not_implemented_error(operator):
        pprint(hole_info)
        raise NotImplementedError(
            f"Could not handle: {operator}."
            "You will need to manually write the grammar for this.")

    if hole_info["ufn"] in default:
        return default[hole_info["ufn"]]
    elif "!" in ground_truth:
        return handle_array_operator()
    elif "=" in ground_truth:
        return handle_eq_operator("=")
    elif "#" in ground_truth:
        return handle_eq_operator("#")
    elif "\\in" in ground_truth:
        return handle_in_operator("\\in")
    elif "\\notin" in ground_truth:
        return handle_in_operator("\\notin")
    elif "\\subseteq" in ground_truth:
        return handle_in_operator("\\subseteq")
    elif "[" in ground_truth:
        return handle_array_operator()
    elif "\\cup" in ground_truth:
        return handle_set_operator("\\cup")
    elif "\\cap" in ground_truth:
        return handle_set_operator("\\cap")
    elif "\\" in ground_truth:
        return handle_set_operator("\\")
    else:
        return handle_other_cases(ground_truth)

def get_raw_act_name(act):
    '''Remove (...) from the end of action name.
    '''
    return act["action_name"].split('(')[0]

def get_act_params(act):
    '''Extract the parameters from the action.
    '''
    if "(" not in act["action_name"]:
        return []
    res = act["action_name"].replace(')', '').split('(')[1].split(',')
    # print("before", res)
    res = [p.strip() for p in res if p.strip() != ""]
    # print("after", res)
    return res

def mk_param_maps(hole_info, param_vals):
    '''Extract parameter maps from the hole info.
    '''
    params = get_act_params(hole_info)
    params = [p.strip() for p in params if p.strip() != ""]
    aux = itertools.product(*[param_vals[p] for p in params])
    return [dict(zip(params, a)) for a in aux]

def mk_trivial_grammar(hole_info, return_type, var_types, param_args, default):
    '''Extract the grammar from the hole info. This is very hacky.
    '''
    keep_vars = [v for v in var_types.keys() if v not in param_args]
    keep_vars += [v for v in param_args if v in get_act_params(hole_info)]
    depends = [
        (k,v) for k,v in var_types.items() if k in keep_vars
        # if k in hole_info["gt"].split(" ")
    ]
    grammar = [[
        "Start",
        return_type,
        [mild_ground_truth_parsing(hole_info, var_types, param_args, default)]
    ]]
    return depends, grammar

def mk_trivial_grammar2(hole_info, return_type, var_types, param_args, default):
    '''Extract the grammar from the hole info. This is very hacky.
    '''
    keep = get_act_params(hole_info)
    ignore = [k for k in param_args if k not in keep]
    depends = [
        (k,v) for k,v in var_types.items() 
        if k not in ignore
    ]
    # print("# mk_trivial_grammar2")
    # pprint(hole_info)
    # print("ignore", ignore)
    # print("keep", keep)
    # print("depends", depends)
    # print("param_args", param_args)
    if hole_info["update_var"] is None:
        fail = ("Bool", True)
    else:
        fail = hole_info["update_var"]
    grammar = [[
        "Start",
        return_type,
        [
            fail,
            mild_ground_truth_parsing(hole_info, var_types, param_args, default)
        ]
    ]]
    return depends, grammar

def mk_functar(hole_info, var_types, param_args, default, gfn):

    ufn = hole_info["ufn"]
    if hole_info["update_var"] is None:
        return_type = "Bool"
    else:
        return_type = var_types[hole_info["update_var"]]

    depends, grammar = gfn(
        hole_info, return_type, var_types, param_args, default)

    return [ufn, depends, return_type, grammar]

def mk_hole(hole_info, fair_actions, var_types, param_vals, default, gfn):
    '''Extract hole from the meta file.
    '''

    param_args = list(param_vals.keys())

    hole_name = hole_info["ufn"]
    ground_truth = hole_info["gt"]
    action = get_raw_act_name(hole_info)
    functar = mk_functar(hole_info, var_types, param_args, default, gfn)
    is_fair = action in fair_actions
    is_guard = hole_info["update_var"] is None
    param_maps = mk_param_maps(hole_info, param_vals)

    parsed_ground_truth = mild_ground_truth_parsing(
        hole_info, var_types, param_args, default)

    hole = {
        "functar" : functar,
        "ground_truth" : ground_truth,
        "parsed_ground_truth" : parsed_ground_truth,
        "action" : action,
        "is_fair" : is_fair,
        "is_guard" : is_guard,
        "param_maps" : param_maps,
    }
    return hole_name, hole

def mk_holes(
        sketch_meta, fair_actions, var_types, param_vals, default, gfn=None):
    '''Try to extract holes from the meta file.
    WARNING: if the meta generator skipped some holes or if some holes do
    not exist between the <actions> tags, you will need to add them manually.
    '''
    if gfn is None:
        gfn = mk_trivial_grammar
    res = {k : v for k, v in [
        mk_hole(hole_info, fair_actions, var_types, param_vals, default, gfn) 
        for hole_info in sketch_meta if "ufn" in hole_info]}
    return res

def mk_init_act_params(sketch_meta):
    '''Try to extract parameter actions from the meta file.
    WARNING: if the meta generator skipped some actions or if some actions do
    not exist between the <actions> tags, you will need to add them manually.
    '''
    res = {"Initial predicate" : []}
    for act in sketch_meta:
        # remove (...) from the end of action name
        if "action_name" not in act:
            continue
        raw_act_name = get_raw_act_name(act)
        params = act["action_name"].replace(')', '').split('(')
        if len(params) == 1:
            params = []
        else:
            params = params[1].split(',')
        params = [p.strip() for p in params if p.strip() != ""]
        res[raw_act_name] = params
    return res

# # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # # 
    
if __name__ == "__main__":
    mk_and_write_sketch('mldr_sm')
    # mk_and_write_sketch('mldr')
    # mk_and_write_sketch('lock_serv')
    # mk_and_write_sketch('consensus_epr')
    # mk_and_write_sketch('two_phase_commit')
    # mk_and_write_sketch('peterson')
    # mk_and_write_sketch('sharded_kv')
    # mk_and_write_sketch('simple_decentralized_lock')