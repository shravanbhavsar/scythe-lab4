import sys
import json

import os


ANALYZE_DISCOVERY_DIR = "discovery_output_data"
WRITE_DISCOVERY_DIR = f"../{ANALYZE_DISCOVERY_DIR}"
DATAPOINTS_DIR = f"datapoints"
SKETCH_DIR = f"sketches"
SOLUTION_DIR = f"solutions"
GRAMMAR_DIR = f"grammars"
GT_DIR = f"ground_truth"
META_DIR = f"meta"

def writer(payload, directory, meta):
    '''Write payload and meta to the file:
    directory/jobid_configindex_epoch.json. 

    Meta should be a dictionary containing the following
    keys:
    - jobid
    - configindex
    - epoch

    If meta is None, then payload will be treated as both
    the payload and the meta. In this case, the payload
    should be a dictionary containing the keys above.
    '''

    data = payload
    if meta is not None:
        data = {
            "epoch" : meta["epoch"],
            "jobid" : meta["jobid"],
            "configindex" : meta["configindex"],
            "payload" : payload,
        }

    epoch = data["epoch"]
    jobid = data["jobid"]
    configindex = data["configindex"]

    local_directory = f"{WRITE_DISCOVERY_DIR}/{directory}"
    # Create the directory if it doesn't exist
    if not os.path.exists(local_directory):
        os.makedirs(local_directory)
    path_to_file = f"{directory}/{jobid}_{configindex}_{epoch}.json"
    # Write the data to the file
    with open(f"{WRITE_DISCOVERY_DIR}/{path_to_file}", "w") as f:
        json.dump(data, f)
    return f"{ANALYZE_DISCOVERY_DIR}/{path_to_file}"


def write_solution(payload, directory, meta):
    epoch = meta["epoch"]
    jobid = meta["jobid"]
    configindex = meta["configindex"]

    local_directory = f"{WRITE_DISCOVERY_DIR}/{directory}"
    # Create the directory if it doesn't exist
    if not os.path.exists(local_directory):
        os.makedirs(local_directory)
    path_to_file = f"{directory}/{jobid}_{configindex}_{epoch}.tla"
    # Write the data to the file
    with open(f"{WRITE_DISCOVERY_DIR}/{path_to_file}", "w") as f:
        f.write(payload)

def main(argv):

    from main_full_2pc import mk_run_experiment_2pc as mk_run_experiment_2pc_big
    from main_lock_serv import mk_run_experiment_lock_serv
    from main_consensus_epr import mk_run_experiment_consensus_epr
    from main_two_phase_commit import mk_run_experiment_2pc as mk_run_experiment_2pc_small
    from main_simple_decentralized_lock import mk_run_experiment_simple_decentralized_lock
    from main_sharded_kv import mk_run_experiment_sharded_kv
    from main_peterson import mk_run_experiment_peterson
    from main_mldr import mk_run_experiment_mldr
    from main_mldr_sm import mk_run_experiment_mldr_sm

    print("Starting experiment...")
    if len(argv) != 4:
        msg = (
            "Usage: python benchmark.py <configfile> <table ID> <optimize=0|1>")
        raise ValueError(msg)
    if not argv[2].isnumeric():
        msg = f"configindex must be numeric, got: {argv[2]}"
        raise ValueError(msg)
    configindex = int(argv[2])
    jobid = 0
    epoch = 0
    optimize = True if argv[3] == "1" else False
    print("configindex:", configindex)

    with open(argv[1]) as f:
        configs = json.load(f)
    config = configs[configindex]
    protocol = config["protocol"]
    holes = config["holes"]
    maxconfigid = config["maxconfigid"]
    timeout = config.get("timeout", None)
    # optimize = config.get("optimize", None)
    init_configid = config.get("init_configid", None)
    extracheck = config.get("extracheck", False)

    print("protocol:", protocol)
    print("holes:", holes)

    if protocol == "2pc_big":
        data = mk_run_experiment_2pc_big(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "lock_serv":
        data = mk_run_experiment_lock_serv(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "consensus_epr":
        data = mk_run_experiment_consensus_epr(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "2pc_small":
        data = mk_run_experiment_2pc_small(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "simple_decentralized_lock":
        data = mk_run_experiment_simple_decentralized_lock(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "sharded_kv":
        data = mk_run_experiment_sharded_kv(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "peterson":
        data = mk_run_experiment_peterson(
            holes, timeout=timeout, optimize=optimize)
    elif protocol == "mldr":
        data = mk_run_experiment_mldr(
            holes, timeout=timeout, optimize=optimize, extracheck=extracheck)
    elif protocol == "mldr_sm":
        data = mk_run_experiment_mldr_sm(
            holes, timeout=timeout, optimize=optimize, extracheck=extracheck)
    else:
        raise ValueError(f"Unknown protocol: {protocol}")
    
    data["maxconfigid"] = maxconfigid
    data["configindex"] = configindex
    data["jobid"] = jobid
    data["epoch"] = epoch
    data["timeout (s)"] = timeout
    data["protocol"] = protocol
    data["init_configid"] = init_configid
    data["extracheck"] = extracheck

    sketch = data["sketch"]
    path_to_sketch = writer(sketch, SKETCH_DIR, meta=data)
    data["sketch"] = path_to_sketch

    solution = data["solution"]
    # path_to_solution = writer(solution, SOLUTION_DIR, meta=data)
    # data["solution"] = path_to_solution
    write_solution(solution, SOLUTION_DIR, meta=data)

    grammar = data["grammar"]
    path_to_grammar = writer(grammar, GRAMMAR_DIR, meta=data)
    data["grammar"] = path_to_grammar

    gt_tla = data["ground truth tla"]
    path_to_gt_tla = writer(gt_tla, GT_DIR, meta=data)
    data["ground truth tla"] = path_to_gt_tla

    epoch = writer(data, DATAPOINTS_DIR, meta=None)

if __name__ == "__main__":
    main(sys.argv)