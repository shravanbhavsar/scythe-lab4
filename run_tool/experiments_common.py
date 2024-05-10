from pprint import pprint


try:
    from .tool.naive_learner.candidate_space import CandidateSpace as NaiveCandidateSpace
    # from cvc5_interface.candidate_space import CandidateSpace as CVC5CandidateSpace
    from .tool.constraint_inference import make_constraints, constraints_size
    from .tool.tlc_interface.model_checking import model_check
    from .tool.tlc_interface.violations import pprint_violation, violation_size
    from .tool.naive_learner.grammar_enum import size_fn
except:
    from tool.naive_learner.candidate_space import CandidateSpace as NaiveCandidateSpace
    # from cvc5_interface.candidate_space import CandidateSpace as CVC5CandidateSpace
    from tool.constraint_inference import make_constraints, constraints_size
    from tool.tlc_interface.model_checking import model_check
    from tool.tlc_interface.violations import pprint_violation, violation_size
    from tool.naive_learner.grammar_enum import size_fn
import time
from call_function_with_timeout import SetTimeout


def mk_k_holes(holes, k):
    if isinstance(holes, dict):
        holes = list(holes.keys())
    if len(holes) < k:
        return []
    argss = [holes[i:] for i in range(k)]
    zs = zip(*argss)
    return list(zs)

def mk_experiment(
        sketch, all_holes, holes_to_poke, constants, assumes, logic=None, 
        learner=None, optimize=None):
    if learner == "naive":
        CandidateSpace = NaiveCandidateSpace
    else:
        raise ValueError(f"Unknown learner: {learner}")
        # CandidateSpace = CVC5CandidateSpace
    if logic is None:
        logic = "ALIAFS"
    for hole_name in all_holes:
        if hole_name not in holes_to_poke:
            sketch = sketch.replace(
                hole_name, all_holes[hole_name]["ground_truth"])
    
    functars = [all_holes[hole_name]["functar"] for hole_name in holes_to_poke]
    holes_infos = {
        hole_name : {
            "is_guard" : all_holes[hole_name]["is_guard"],
            "action" : all_holes[hole_name]["action"],
        }
        for hole_name in holes_to_poke
    }
    
    print("Creating candidate space...", flush=True)
    universe = CandidateSpace(
        sketch, functars, constants, logic=logic, hole_infos=holes_infos,
        assumptions=assumes, optimize=optimize)
    # print("REMOVE_ME")
    # universe.prune(test)
    for hole_name in holes_to_poke:
        all_holes[hole_name]["depends"] = all_holes[hole_name]["functar"][1]
    return universe, all_holes

def iteration(cnt, universe, tla_module, tla_config, act_params, experiment_configs, ground_truth, inner_timeout,
        tla_config2=None, discard_violation2=False):
    
    cumm_constraint_subterms = []
    times_to_pick_candidate = []
    cumm_constraint_subterms_val = 0
    times_to_model_check = []
    cumm_violation_transitions_val = 0
    cnt += 1

    print(f"Picking candidate {cnt}", flush=True)
    print(f"Picking candidate {cnt}", end="", flush=True)
    pick_start = time.time()
    candidate, interpretations = universe.pick(timeout=inner_timeout)
    # print(candidate)
    pick_end = time.time()
    if candidate is None:
        raise ValueError("No more candidates to pick.")
        return (
            False,
            cnt,
            cumm_constraint_subterms,
            times_to_pick_candidate,
            cumm_constraint_subterms_val,
            times_to_model_check,
            cumm_violation_transitions_val,
            None,
            None)
    print("Candidate picked:", flush=True)
    # pprint(interpretations)
    print(interpretations, flush=True)
    # print(candidate)
    print(f"Time to pick candidate: {pick_end - pick_start}", flush=True)
    times_to_pick_candidate.append(pick_end - pick_start)
    
    print("Model chcking candidate...", flush=True)
    mc_start = time.time()
    violation = model_check(
        tla_module, candidate, tla_config, act_params)
    mc_end = time.time()
    mc_duration1 = mc_end - mc_start
    mc_duration2 = 0
    if violation is None:
        if tla_config2 is not None:
            print(
                "The first model checking run succeeded, no violation was" 
                " found. A second config, probably w/o symmetry reduction or"
                " with larger parameters, was"
                " provided. Running a second round of model checking.")
            mc_start = time.time()
            violation = model_check(
                tla_module, candidate, tla_config2, act_params)
            mc_end = time.time()
            mc_duration2 = mc_end - mc_start
    mc_duration = mc_duration1 + mc_duration2
    times_to_model_check.append(mc_duration)
    if violation is None:
        print("Success, no violation found!", flush=True)
        print("Time to model check: ", mc_duration, flush=True)
        print(flush=True)
        print("Ground truth:")
        # pprint(ground_truth)
        print(ground_truth, flush=True)
        print("\n\n", flush=True)
        return (
            True,
            cnt,
            cumm_constraint_subterms,
            times_to_pick_candidate,
            cumm_constraint_subterms_val,
            times_to_model_check,
            cumm_violation_transitions_val,
            candidate,
            interpretations)
    else:
        if mc_duration2 != 0:
            print("The first model checking passed and the second failed.")
        vsize = violation_size(violation)
        print(f"Violation found; some statistics:", flush=True)
        print(f"    Violation type: {violation.sort}", flush=True)
        print(f"    Violation size: {vsize}", flush=True)
        print(f"    Time to model check: {mc_duration}", flush=True)
    cumm_violation_transitions_val += vsize
    # pprint_violation(violation)
    
    ufn_args = {}
    for ufn in interpretations:
        interpretation = interpretations[ufn]
        ufn_args[ufn] = {
            "action" : experiment_configs[ufn]["action"],
            "is_fair" : experiment_configs[ufn]["is_fair"],
            "is_guard" : experiment_configs[ufn]["is_guard"],
            "depends" : experiment_configs[ufn]["depends"],
            "param_maps" : experiment_configs[ufn]["param_maps"],
            "interpretation" : interpretation,
        }
    if not discard_violation2 or mc_duration2 == 0:
        constraints_start = time.time()
        con = make_constraints(
            violation, ufn_args, constant_map=universe.get_constant_map())
        constraints_end = time.time()
        # pprint(con)
        con_size = constraints_size(con)
        cumm_constraint_subterms_val += con_size
        cumm_constraint_subterms.append(cumm_constraint_subterms_val)
        print("Constraints generated; some statistics:", flush=True)
        print(f"    Number of subterms: {constraints_size(con)}", flush=True)
        print(f"    Time to generate constraints: {constraints_end - constraints_start}", flush=True)
        # print(list(zip(cumm_constraint_subterms, times_to_pick_candidate)))
        # pprint(con)

        print("Pruning...", flush=True)
        universe.prune(con)
        print("Done.", flush=True)
        print(flush=True)
    else:
        print("Discarding counter-example from second model checking run.")
    return (
        False,
        cnt,
        cumm_constraint_subterms,
        times_to_pick_candidate,
        cumm_constraint_subterms_val,
        times_to_model_check,
        cumm_violation_transitions_val,
        None,
        None)

def run_experiment(
        tla_module, universe, experiment_configs, tla_config, act_params, 
        ground_truth=None, timeout=None, tla_config2=None, 
        discard_violation2=False):

    if isinstance(timeout, str):
        if not timeout.isnumeric():
            raise ValueError(
                f"Expected timeout str to be numeric got {timeout}")
        timeout = int(timeout)

    if ground_truth is None:
        ground_truth = "Not specified"

    cnt = 0
    cumm_constraint_subterms = []
    times_to_pick_candidate = []
    cumm_constraint_subterms_val = 0
    times_to_model_check = []
    cumm_violation_transitions_val = 0
    start_tot = time.time()
    done = False

    candidate = None
    interpretations = None
    while not done:
        elapsed = (time.time() - start_tot)
        inner_timeout = None
        if timeout is not None:
            inner_timeout = timeout - elapsed
        timeout_iteration = SetTimeout(iteration, inner_timeout)

        if inner_timeout is not None and inner_timeout < 0:
            print("Timed out!!", flush=True)
            break

        print("Starting next iteration.", flush=True)
        res = timeout_iteration(
            cnt, universe, tla_module, tla_config, act_params, 
            experiment_configs, ground_truth, inner_timeout,
            tla_config2=tla_config2, discard_violation2=discard_violation2)
        
        done, _, error_trace, res = res
        if not done:
            if error_trace != '':
                print(error_trace)
                raise RuntimeError("")
            print("Timed out!!", flush=True)
            break

        (
            done,
            cnt,
            nxt_cumm_constraint_subterms,
            nxt_times_to_pick_candidate,
            nxt_cumm_constraint_subterms_val,
            nxt_times_to_model_check,
            nxt_cumm_violation_transitions_val,
            candidate,
            interpretations) = res
        
        cumm_constraint_subterms += nxt_cumm_constraint_subterms
        times_to_pick_candidate += nxt_times_to_pick_candidate
        cumm_constraint_subterms_val += nxt_cumm_constraint_subterms_val
        times_to_model_check += nxt_times_to_model_check
        cumm_violation_transitions_val += nxt_cumm_violation_transitions_val
        
    end_tot = time.time()
    tot_time = end_tot - start_tot
    tot_model_check_time = sum(times_to_model_check)
    tot_candidate_pick_time = sum(times_to_pick_candidate)

    # return tot_time, tot_model_check_time, tot_candidate_pick_time, cnt
    return {
        "found correct completion" : done,
        "total time" : tot_time,
        "time model checking" : tot_model_check_time,
        "time picking candidates" : tot_candidate_pick_time,
        "# candidates model checked" : cnt,
        "solution" : candidate,
        "interpretations" : interpretations,
        "total constraint terms" : cumm_constraint_subterms_val,
        "total violation trans" : cumm_violation_transitions_val,
    }

def pprint_data(data):
    cnt = data['# candidates model checked']
    cand_space_size = data["search space size"]
    elim = data["# candidates eliminated before model checking"]
    print("\nSummary:", flush=True)
    print("  Timing:", flush=True)
    print(f"    Total: {data['total time']}", flush=True)
    mc_time = data['total time'] - data['time picking candidates']
    print(f"    Model checking: {mc_time}", flush=True)
    print("  Generated:", flush=True)
    print(f"    # candidates model checked: {cnt}", flush=True)
    print(f"    # Candidates eliminated before model checking: {elim}", flush=True)
    print(f" Solution at: see run_tool/README.md", flush=True)
    print("\n\n\n", flush=True)

def mk_run_experiment(
        sketch, holes, holes_to_poke, constants, assumes, tla_module, 
        tla_config, act_params, logic=None, learner=None, timeout=None,
        tla_config2=None, discard_violation2=False, 
        optimize=None):
    for hole in holes_to_poke:
        if hole not in holes:
            raise ValueError(f"Hole {hole} not in {holes.keys()}")
    universe, experiment_configs = mk_experiment(
        sketch, holes, holes_to_poke, constants, assumes, logic=logic, 
        learner=learner, optimize=optimize)
    ground_truth = {
        k : v["ground_truth"] for k, v in holes.items() if k in holes_to_poke}
    data = run_experiment(
        tla_module, universe, experiment_configs, tla_config, act_params, 
        ground_truth=ground_truth, timeout=timeout, tla_config2=tla_config2,
        discard_violation2=discard_violation2)
    parsed_ground_truth = {
        k : v.get("parsed_ground_truth", None) 
        for k, v in holes.items() if k in holes_to_poke}
    
    data["optimized"] = optimize
    data["ground truth"] = ground_truth
    data["parsed ground truth"] = parsed_ground_truth
    data["sketch"] = universe.sketch
    data["grammar"] = universe.get_grammars()
    k, v = list(universe.get_grammars().items())[0]
    g_size = 0
    for k, v in universe.get_grammars().items():
        for x in v:
            # print(x)
            # print(size_fn(x))
            g_size += size_fn(x)
    data["grammar size"] = g_size
    # print(f"Grammar size: {g_size}")
    # assert(False)
    data["ground truth tla"] = universe._instantiate_sketch(parsed_ground_truth)
    data["search space size"] = universe.get_size()
    data["final search size (n)"] = universe.expr_size

    m = sum(size_fn(v) for k, v in parsed_ground_truth.items())
    data["ground truth size (m)"] = m
    print(f"Performing expensive count operation (={m})...", flush=True)
    t = time.time()
    b1, b2, e, eq_m = SetTimeout(universe.count_exprs, 120)(m)
    if b2:
        eq_m = None
    data["candidates of size =m"] = eq_m
    print(f"Finished counting in {time.time()-t} sec.", flush=True)
    print(f"Performing expensive count operation (<{m})...", flush=True)
    lt_m_fn = lambda: sum(
        universe.count_exprs(i) for i in range(1, m))
    t = time.time()
    b1, b2, e, lt_m = SetTimeout(lt_m_fn, 120)()
    if b2:
        lt_m = None
    data["candidates of size <m"] = lt_m
    print(f"Finished counting in {time.time()-t} sec.", flush=True)


    data["# candidates eliminated before model checking"] = (
        universe.get_eliminated())
    data["# holes"] = len(holes_to_poke)
    data["holes"] = holes_to_poke
    n_guards = len([k for k in holes_to_poke if holes[k]["is_guard"]])
    n_updates = len([k for k in holes_to_poke if not holes[k]["is_guard"]])
    data["# pre/post holes"] = f"{n_guards} / {n_updates}"
    # format the date and time in yyyy-MM-dd-hh-mm-ss format
    timestamp = time.strftime("%Y-%m-%d-%H-%M-%S", time.gmtime())
    data["finished timestamp"] = timestamp
    pprint_data(data)
    return data
