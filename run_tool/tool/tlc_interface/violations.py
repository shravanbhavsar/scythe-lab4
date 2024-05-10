from dataclasses import dataclass
from typing import Union
from pprint import pprint

DEADLOCK = "deadlock"
LIVENESS = "liveness"
SAFETY = "safety"
ACTION = "action"
STUTTERING = "stuttering (liveness)"

@dataclass
class TLCTransition:
    action: str
    params: dict[str,str]
    src: str
    tgt: str

@dataclass
class TLCViolation:
    states: dict[str, dict[str, str]]
    init: str
    delta: dict[str,TLCTransition]
    raw: list[str]
    sort: str


# Some ad hoc parsing of TLC error traces. 

def include_line(line, all_lines):
    if line.startswith("State"):
        return True
    if line.startswith("  "):
        return True
    if line.startswith("Back to state"):
        return True
    if line.startswith("/"):
        return True
    if line.startswith("Error: Deadlock"):
        return True
    if line.startswith("Error: Parsing"):
        pprint(all_lines)
        raise RuntimeError("TLC was unable to parse the tla string.")
    if line.startswith("Error: TLC threw an unexpected"):
        pprint(all_lines)
        raise RuntimeError("TLC threw an unexpected exception.")
    if line.startswith("Error: "):
        return True
    return False

def post_process_states(
        states : list[tuple[str, dict[str, str]]], raw, sort, raw_lines
        ) -> TLCViolation:
    aux = dict(states)
    succs = dict(zip([x for x,y in states], [x for x,y in states][1:]))
    if len(states) == 0:
        pprint(raw_lines)
        raise ValueError("Expected at least one state in violation trace.")
    init = states[0][0]
    delta = {}
    for src, tgt in succs.items():
        src_info = aux[src]
        tgt_info = aux[tgt]
        if tgt.startswith("Back"):
            tgt = tgt.replace("Back to ", "").replace("state", "State")
            if tgt not in aux:
                raise ValueError(
                    f"Invalid back pointer in liveness violation: {tgt}")
            for k,v in aux[tgt].items():
                # This is important
                if k in ["_action", "_params"]:
                    continue
                tgt_info[k] = v
        action = tgt_info["_action"]
        params = tgt_info["_params"]
        if not isinstance(params, dict):
            raise ValueError("Expected params to be a dictionary.")
        if action == "Stuttering":
            tgt = src
            # Note: before setting tgt to src, tgt referred to a
            # different state with no assignments to the state variables
            # that is now unreachable.
        transition = TLCTransition(action, params, src, tgt)
        delta[src] = transition
    processed_states = {}
    for idx, state in aux.items():
        if idx in processed_states:
            raise ValueError(f"Duplicate state index: {idx}")
        processed_states[idx] = {}
        for k,v in state.items():
            if k not in ["_action", "_params"]:
                processed_states[idx][k] = v     

    return TLCViolation(processed_states, init, delta, raw, sort)

def parse_state(
        tlc_lines : list[str], 
        raw_lines : list[str],
        params_map) -> tuple[str, dict[str, str]]:
    result = {}
    header = tlc_lines[0]
    tail = tlc_lines[1:]
    header = header.split("line")[0]
    header = header.replace("<", "").replace(">", "")
    header_left, header_right = header.split(":")
    if "$$" in header_right:
        aux = header_right.split("$$")
        action = aux[1]
        params = aux[2:-1]
    else:
        action = header_right
        params = []
    action = action.strip()
    if action not in params_map and action != "Stuttering":
        raise ValueError(f"Unexpected action: {action}")
    if len(params_map.get(action, [])) != len(params):
        pprint(params)
        pprint(params_map.get(action, []))
        raise ValueError(
            f"Expected action {action} to have {len(params)} params")
    params = dict(zip(params_map.get(action, []), params))
    result["_action"] = action.strip()
    result["_params"] = params
    new_tail = []
    for line in tail:
        if line.startswith("/\\"):
            new_tail.append(line)
        elif line.startswith("  "):
            new_tail[-1] += line
    tail = new_tail
    for line in tail:
        line = line.replace(" ", "").replace("/\\", "")
        try:
            line_left, line_right = line.split("=")
        except ValueError as e:
            pprint(raw_lines)
            print(line)
            raise e
        result[line_left] = line_right
    return (header_left, result)

def parse_states(
        tlc_lines : list[str], raw_lines, errors, params_map) -> TLCViolation:
    block_idxs = [
        idx for idx, x in enumerate(tlc_lines) 
        if x.startswith("State ") or x.startswith("Back to state ")]
    block_idxs.append(len(tlc_lines))
    # This is may fail if block_idxs is of size 1. Note sure if possible.
    state_endpoints = list(zip(block_idxs, block_idxs[1:]))
    state_blocks = [tlc_lines[start:end] for start, end in state_endpoints]
    parsed_states = [
        parse_state(x, raw_lines, params_map) for x in state_blocks]

    if any("Deadlock" in e for e in errors):
        sort = DEADLOCK
    elif any("Stuttering" in line for line in tlc_lines):
        sort = STUTTERING
    elif any("Temporal" in e for e in errors):
        sort = LIVENESS
    elif any("Invariant" in e for e in errors):
        sort = SAFETY
    elif any("Action property" in e for e in errors):
        sort = ACTION
    else:
        pprint(raw_lines)
        print(errors)
        raise ValueError("Unrecognized violation type.")

    tmp = post_process_states(parsed_states, tlc_lines, sort, raw_lines)
    # pprint(tmp)
    return tmp

def parse_violation(
        tlc_lines : list[str], params_map) -> Union[TLCViolation, None]:
    # Iterate through the lines until we find the start of the error trace.
    # pprint(tlc_lines)
    raw_lines = list(tlc_lines)
    # pprint(tlc_lines)
    tlc_lines = [x for x in tlc_lines if include_line(x, tlc_lines)]
    final_idx = None
    for idx, line in enumerate(tlc_lines):
        if line.startswith("Error: "):
            final_idx = idx
            break
    if final_idx is None:
        return None
    tlc_lines = tlc_lines[final_idx:]
    error_messages = [x for x in tlc_lines if x.startswith("Error: ")]
    states = parse_states(tlc_lines, raw_lines, error_messages, params_map)
    # pprint_violation(states)
    # print(states)
    # pprint(raw_lines)
    return states



# The following functions are not critical for parsing violations.
# They are used as helper functions for manipulating violations.

def violation_size(violation : TLCViolation):
    return len(list(violation_traversal(violation)))

def violation_traversal(violation : TLCViolation):
    visited = set()
    curr = violation.init
    while curr not in visited and curr in violation.delta:
        visited.add(curr)
        # state = violation.states[curr]
        yield violation.delta[curr]
        curr = violation.delta[curr].tgt   

def get_cycle(violation : TLCViolation) -> Union[None, TLCViolation]:
    '''Return the cycle of the violation if it exists.
    '''
    visited = set()
    curr = violation.init
    while curr not in visited and curr in violation.delta:
        visited.add(curr)
        state = violation.states[curr]
        curr = violation.delta[curr].tgt  
    if curr not in violation.delta:
        return None
    init = curr
    states = dict()
    delta = dict()
    while curr not in states:
        states[curr] = violation.states[curr]
        delta[curr] = violation.delta[curr]
        curr = violation.delta[curr].tgt
    res = TLCViolation(states, init, delta, violation.raw, violation.sort)
    return res

def get_deadlocked_state(violation : TLCViolation):
    if violation.sort != DEADLOCK:
        raise ValueError("Expected deadlock violation.")
    curr_state = violation.init
    for transition in violation_traversal(violation):
        curr_state = transition.tgt
    return curr_state

def pprint_transition(violation : TLCViolation, transition : TLCTransition):
    src = violation.states[transition.src]
    tgt = violation.states[transition.tgt]
    print(transition.src)
    pprint(src)
    print()
    if len(transition.params) > 0:
        print(f"{transition.action}({', '.join(transition.params)})")
    else:
        print(f"{transition.action}")
    print()
    print(transition.tgt)
    pprint(tgt)


def pprint_violation(violation : TLCViolation):
    for transition in violation_traversal(violation):
        pprint_transition(violation, transition)
        print()
        print()
        print()