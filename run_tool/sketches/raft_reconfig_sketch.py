from pathlib import Path

dir_path = Path(__file__).parent.absolute()
sketch = open(dir_path / 'raft_reconfig_sketch.tla', "r").read()
config = open(dir_path / 'raft_reconfig.cfg', "r").read()

const = [
    ("n1", "Int"), ("n2", "Int"), ("n3", "Int"), 
    # ("v1", "Int"), ("v2", "Int"),
    # ("Node", ("Set", "Int")), ("Value", ("Set", "Int")), 
    ("Primary", "Int"),
    ("Secondary", "Int"),
    ("Nil", "Int"),
    ("Quorum", ("Set", ("Set", "Int"))),
]

assumes = [
    ["!=","n1","n2","n3"],
    ["!=","Primary","Secondary","Nil"],
    # ["=","Node",["set.union",["set.singleton","n1"],["set.singleton","n2"],["set.singleton","n3"]]],
    # ["=","Value",["set.union",["set.singleton","v1"],["set.singleton","v2"]]],
    [
        "=",
        "Quorum", 
        [
            "set.union",
            ["set.singleton", 
                ["set.union", 
                ["set.singleton", "n1"], ["set.singleton", "n2"]]],
            ["set.union", 
                ["set.singleton", 
                    ["set.union", 
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]], 
                ["set.singleton", 
                    ["set.union", 
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]]],
        ],
    ],
]

act_params = {
    "Initial predicate" : [],
    # "ClientRequest" : ["i"],
    "GetEntriesAction" : ["i", "j"],
    "RollbackEntries" : ["i", "j"],
    "BecomeLeader" : ["i", "voters"],
    "CommitEntry" : ["i", "commitNodes"],
    "UpdateTerms" : ["i", "j"],
    "Reconfig" : ["i", "newConfig"],
    "SendConfig" : ["i", "j"]
}

# param_types = {
#     "src" : ["n1", "n2", "n3"],
#     "dst" : ["n1", "n2", "n3"],
#     # "n" : ["n1", "n2", "n3"],
#     # "Q" : [["n1", "n2"], ["n1", "n3"], ["n2", "n3"]],
#     # "v" : ["v1", "v2"],
# }

param_maps = [
]

grammar_u1 = [
    ['Start', 'Bool',
        [
            ("Bool", False),
            ["not", ["set.member", "i", "voters"]],
        ]],
]
functar_u1 = [
    "__u1__", 
    [
     ["i", ("Int")], 
     ["voters", ("Set", "Int")], 
     ["config", ("Array", "Int", ("Set", "Int"))], 
     ["configTerm", ("Array", "Int", "Int")],
     ["configVersion", ("Array", "Int", "Int")]
     ], 
    "Bool",
    grammar_u1
]
ground_truth_u1 = 'TRUE'
action_u1 = "BecomeLeader"
is_fair_u1 = True
is_guard_u1 = True

grammar_u2 = [
    ['Start', 'Bool',
        [
            ["=", ["select", "state", "i"], "Secondary"],
            ["=", ["select", "state", "i"], "Primary"],
        ]
    ]
]
functar_u2 = [
    "__u2__", 
    [
     ["i", ("Int")], 
     ["newConfig", ("Set", "Int")], 
     ["state", ("Array", "Int", "Int")], 
     ["config", ("Array", "Int", ("Set", "Int"))], 
     ["configTerm", ("Array", "Int", "Int")],
     ["configVersion", ("Array", "Int", "Int")]
     ], 
    "Bool",
    grammar_u2
]
ground_truth_u2 = 'state[i] = Primary'
action_u2 = "Reconfig"
is_fair_u2 = True
is_guard_u2 = True

'''See two_phase_commit_sketch.py for comments on param_maps.
Briefly: it specifices all possible configurations of the arguments of the
action.
'''

holes = {
    "__u1__" : {
        "functar" : functar_u1,
        "ground_truth" : ground_truth_u1,
        "action" : action_u1,
        "is_fair" : is_fair_u1,
        "is_guard" : is_guard_u1,
        "param_maps" : [
            {"i" : "n1", "voters" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"i" : "n1", "voters" : ["set.union", ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"i" : "n1", "voters" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n3"]]},
        ],
    },
    "__u2__" : {
        "functar" : functar_u2,
        "ground_truth" : ground_truth_u2,
        "action" : action_u2,
        "is_fair" : is_fair_u2,
        "is_guard" : is_guard_u2,
        "param_maps" : [
            {"i" : "n1", "newConfig" : ["set.singleton", "n1"]},
            {"i" : "n1", "newConfig" : ["set.singleton", "n2"]},
            {"i" : "n1", "newConfig" : ["set.singleton", "n3"]},
            {"i" : "n1", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"i" : "n1", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"i" : "n1", "newConfig" : ["set.union", ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"i" : "n1", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"], ["set.singleton", "n3"]]},

            {"i" : "n2", "newConfig" : ["set.singleton", "n1"]},
            {"i" : "n2", "newConfig" : ["set.singleton", "n2"]},
            {"i" : "n2", "newConfig" : ["set.singleton", "n3"]},
            {"i" : "n2", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"i" : "n2", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"i" : "n2", "newConfig" : ["set.union", ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"i" : "n2", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"], ["set.singleton", "n3"]]},

            {"i" : "n3", "newConfig" : ["set.singleton", "n1"]},
            {"i" : "n3", "newConfig" : ["set.singleton", "n2"]},
            {"i" : "n3", "newConfig" : ["set.singleton", "n3"]},
            {"i" : "n3", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"i" : "n3", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"i" : "n3", "newConfig" : ["set.union", ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"i" : "n3", "newConfig" : ["set.union", ["set.singleton", "n1"], ["set.singleton", "n2"], ["set.singleton", "n3"]]},

            # also include the empty set.
            {"i" : "n1", "newConfig" : ["emptyset", ("Set", "Int")]},
            {"i" : "n2", "newConfig" : ["emptyset", ("Set", "Int")]},
            {"i" : "n3", "newConfig" : ["emptyset", ("Set", "Int")]},
        ],
    },
}