from pathlib import Path

dir_path = Path(__file__).parent.absolute()
sketch = open(dir_path / 'consensus_epr_sketch.tla', "r").read()
config = open(dir_path / 'consensus_epr.cfg', "r").read()

const = [
    ("n1", "Int"), ("n2", "Int"), ("n3", "Int"), 
    ("v1", "Int"), ("v2", "Int"),
    ("Node", ("Set", "Int")), ("Value", ("Set", "Int")), 
    ("Quorum", ("Set", ("Set", "Int"))),
]

assumes = [
    ["!=","n1","n2","n3"],
    ["=","Node",["set.union",["set.singleton","n1"],["set.singleton","n2"],["set.singleton","n3"]]],
    ["=","Value",["set.union",["set.singleton","v1"],["set.singleton","v2"]]],
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
    "SendRequestVote" : ["src", "dst"],
    "SendVote" : ["src", "dst"],
    "RecvVote" : ["n", "sender"],
    "BecomeLeader" : ["n", "Q"],
    "Decide" : ["n", "v"],
}

grammar_u1 = [
    ['Start', 'Bool',
        [
            ("Bool", False),
            ["not", ["set.member", "src", "voted"]],
        ]],
]
# grammar_u1 = None
functar_u1 = [
    "__u1__", 
    [["voted", ("Set", "Int")], ["src", "Int"]], 
    "Bool",
    grammar_u1
]
ground_truth_u1 = '~ (src \\in voted)'
action_u1 = "SendVote"
is_fair_u1 = True
is_guard_u1 = True

grammar_u2 = [
    ['Start', 'Bool',
        [
            ("Bool", True),
            ["set.subset", 
             "Q",
             ["select", "votes", "n"]], 
        ]
    ]
]
functar_u2 = [
    "__u2__", 
    [
        ["votes", ("Array", "Int", ("Set", "Int"))], 
        ["n", "Int"],
        ["Q", ("Set", "Int")],
    ],
    "Bool",
    grammar_u2
]
ground_truth_u2 = 'Q \\subseteq votes[n]'
action_u2 = "BecomeLeader"
is_fair_u2 = True
is_guard_u2 = True

grammar_u3 = [
    ['Start', ('Array', 'Int', ('Set', 'Int')),
        [
            "decided",
            ["store", "decided", "n", 
                ["set.union", 
                    ["select", "decided", "n"], 
                    ["set.singleton", "v"]]],
        ]
    ]
]
functar_u3 = [
    "__u3__", 
    [
        ["decided", ("Array", "Int", ("Set", "Int"))], 
        ["n", "Int"],
        ["v", "Int"],
    ],
    ("Array", "Int", ("Set", "Int")),
    grammar_u3
]
ground_truth_u3 = '[decided EXCEPT ![n] = decided[n] \\cup {v}]'
action_u3 = "Decide"
is_fair_u3 = True
is_guard_u3 = False

grammar_u4 = [
    ['Start', ('Set', ('Tuple', 'Int', 'Int')),
        [
            (('Set', ('Tuple', 'Int', 'Int')), "emptyset"),
            ["set.singleton", ["tuple", "src", "src"]],
            ["set.union", 
                ["set.singleton", ["tuple", "src", "src"]],
                ["set.singleton", ["tuple", "dst", "dst"]]],
            ["set.union", 
                "vote_msg", 
                ["set.singleton", ["tuple", "src", "dst"]]],
        ]
    ]
]
functar_u4 = [
    "__u4__",
    [
        ["vote_msg", ("Set", ("Tuple", "Int", "Int"))],
        ["src", "Int"],
        ["dst", "Int"],
    ],
    ("Set", ("Tuple", "Int", "Int")),
    grammar_u4
]
ground_truth_u4 = 'vote_msg \\cup {<<src, dst>>}'
action_u4 = "SendVote"
is_fair_u4 = True
is_guard_u4 = False

grammar_u5 = [
    ['Start', ('Set', ('Tuple', 'Int', 'Int')),
        [
            (('Set', ('Tuple', 'Int', 'Int')), "emptyset"),
            ["set.singleton", ["tuple", "src", "src"]],
            ["set.union",
                ["set.singleton", ["tuple", "src", "src"]],
                ["set.singleton", ["tuple", "dst", "dst"]]],
            ["set.union",
                "vote_request_msg",
                ["set.singleton", ["tuple", "src", "dst"]]],
        ]
    ]
]
functar_u5 = [
    "__u5__",
    [
        ["vote_request_msg", ("Set", ("Tuple", "Int", "Int"))],
        ["src", "Int"],
        ["dst", "Int"],
    ],
    ("Set", ("Tuple", "Int", "Int")),
    grammar_u5
]
ground_truth_u5 = 'vote_request_msg \\cup {<<src, dst>>}'
action_u5 = "SendRequestVote"
is_fair_u5 = True
is_guard_u5 = False

grammar_u6 = [
    ['Start', ("Set", "Int"),
        [
            (("Set", "Int"), "emptyset"),
            "leader",
            ["set.union", "leader", "Q"],
            ["set.union", "leader", ["set.singleton", "n"]],
        ]
    ]
]
functar_u6 = [
    "__u6__",
    [
        ["leader", ("Set", "Int")],
        ["n", "Int"],
        ["Q", ("Set", "Int")],
    ],
    ("Set", "Int"),
    grammar_u6
]
ground_truth_u6 = 'leader \\cup {n}'
action_u6 = "BecomeLeader"
is_fair_u6 = True
is_guard_u6 = False

grammar_u7 = [
    ['Start', ("Array", "Int", ("Set", "Int")),
        [
            "votes",
            ["store", "votes", "Int", 
                ["set.union", 
                    ["select", "votes", "Int"],
                    ["set.singleton", "Int"]],
            ]
        ]
    ],
    ['Int', 'Int', ["n", "sender"]],
]
functar_u7 = [
    "__u7__",
    [
        ["votes", ("Array", "Int", ("Set", "Int"))],
        ["n", "Int"],
        ["sender", "Int"],
    ],
    ("Array", "Int", ("Set", "Int")),
    grammar_u7
]
ground_truth_u7 = '[votes EXCEPT ![n] = votes[n] \\cup {sender}]'
action_u7 = "RecvVote"
is_fair_u7 = True
is_guard_u7 = False

grammar_u8 = [
    ['Start', ("Set", "Int"),
        [
            (("Set", "Int"), "emptyset"),
            "voted",
            ["set.minus", "voted", ["set.singleton", "Int"]],
            ["set.union", "voted", ["set.singleton", "Int"]],
        ]
    ],
    ['Int', 'Int', ["dst", "src"]],
]
functar_u8 = [
    "__u8__",
    [
        ["voted", ("Set", "Int")],
        ["dst", "Int"],
        ["src", "Int"],
    ],
    ("Set", "Int"),
    grammar_u8
]
ground_truth_u8 = 'voted \\cup {src}'
action_u8 = "SendVote"
is_fair_u8 = True
is_guard_u8 = False

grammar_u9 = [
    ['Start', 'Bool',
        [
            ("Bool", True),
            ["set.member", ["tuple", "Int", "Int"], "vote_request_msg"],
        ]
    ],
    ['Int', 'Int', ["src", "dst"]],
]
functar_u9 = [
    "__u9__",
    [
        ["vote_request_msg", ("Set", ("Tuple", "Int", "Int"))],
        ["src", "Int"],
        ["dst", "Int"],
    ],
    "Bool",
    grammar_u9
]
ground_truth_u9 = '<<dst, src>> \\in vote_request_msg'
action_u9 = "SendVote"
is_fair_u9 = True
is_guard_u9 = True

grammar_u10 = [
    ['Start', 'Bool',
        [
            ("Bool", True),
            ["set.member", ["tuple", "Int", "Int"], "vote_msg"],
        ]
    ],
    ['Int', 'Int', ["n", "sender"]],
]
functar_u10 = [
    "__u10__",
    [
        ["vote_msg", ("Set", ("Tuple", "Int", "Int"))],
        ["n", "Int"],
        ["sender", "Int"],
    ],
    "Bool",
    grammar_u10
]
ground_truth_u10 = '<<sender, n>> \\in vote_msg'
action_u10 = "RecvVote"
is_fair_u10 = True
is_guard_u10 = True


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
            {"src" : "n1", "dst" : "n1"},
            {"src" : "n1", "dst" : "n2"},
            {"src" : "n1", "dst" : "n3"},
            {"src" : "n2", "dst" : "n1"},
            {"src" : "n2", "dst" : "n2"},
            {"src" : "n2", "dst" : "n3"},
            {"src" : "n3", "dst" : "n1"},
            {"src" : "n3", "dst" : "n2"},
            {"src" : "n3", "dst" : "n3"},
        ],
    },
    "__u2__" : {
        "functar" : functar_u2,
        "ground_truth" : ground_truth_u2,
        "action" : action_u2,
        "is_fair" : is_fair_u2,
        "is_guard" : is_guard_u2,
        "param_maps" : [
            {"n" : "n1", 
             "Q" : ["set.union", 
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n1",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n1",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
             
        ],
    },
    "__u3__" : {
        "functar" : functar_u3,
        "ground_truth" : ground_truth_u3,
        "action" : action_u3,
        "is_fair" : is_fair_u3,
        "is_guard" : is_guard_u3,
        "param_maps" : [
            {"n" : "n1", "v" : "n1"},
            {"n" : "n1", "v" : "n2"},
            {"n" : "n1", "v" : "n3"},
            {"n" : "n2", "v" : "n1"},
            {"n" : "n2", "v" : "n2"},
            {"n" : "n2", "v" : "n3"},
            {"n" : "n3", "v" : "n1"},
            {"n" : "n3", "v" : "n2"},
            {"n" : "n3", "v" : "n3"},
        ],
    },
    "__u4__" : {
        "functar" : functar_u4,
        "ground_truth" : ground_truth_u4,
        "action" : action_u4,
        "is_fair" : is_fair_u4,
        "is_guard" : is_guard_u4,
        "param_maps" : [
            {"src" : "n1", "dst" : "n1"},
            {"src" : "n1", "dst" : "n2"},
            {"src" : "n1", "dst" : "n3"},
            {"src" : "n2", "dst" : "n1"},
            {"src" : "n2", "dst" : "n2"},
            {"src" : "n2", "dst" : "n3"},
            {"src" : "n3", "dst" : "n1"},
            {"src" : "n3", "dst" : "n2"},
            {"src" : "n3", "dst" : "n3"},
        ],
    },
    "__u5__" : {
        "functar" : functar_u5,
        "ground_truth" : ground_truth_u5,
        "action" : action_u5,
        "is_fair" : is_fair_u5,
        "is_guard" : is_guard_u5,
        "param_maps" : [
            {"src" : "n1", "dst" : "n1"},
            {"src" : "n1", "dst" : "n2"},
            {"src" : "n1", "dst" : "n3"},
            {"src" : "n2", "dst" : "n1"},
            {"src" : "n2", "dst" : "n2"},
            {"src" : "n2", "dst" : "n3"},
            {"src" : "n3", "dst" : "n1"},
            {"src" : "n3", "dst" : "n2"},
            {"src" : "n3", "dst" : "n3"},
        ],
    },
    "__u6__" : {
        "functar" : functar_u6,
        "ground_truth" : ground_truth_u6,
        "action" : action_u6,
        "is_fair" : is_fair_u6,
        "is_guard" : is_guard_u6,
        "param_maps" : [
            {"n" : "n1", 
             "Q" : ["set.union", 
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n1",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n1",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n2",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n2"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n1"], ["set.singleton", "n3"]]},
            {"n" : "n3",
             "Q" : ["set.union",
                    ["set.singleton", "n2"], ["set.singleton", "n3"]]},
        ],
    },
    "__u7__" : {
        "functar" : functar_u7,
        "ground_truth" : ground_truth_u7,
        "action" : action_u7,
        "is_fair" : is_fair_u7,
        "is_guard" : is_guard_u7,
        "param_maps" : [
            {"n" : "n1", "sender" : "n1"},
            {"n" : "n1", "sender" : "n2"},
            {"n" : "n1", "sender" : "n3"},
            {"n" : "n2", "sender" : "n1"},
            {"n" : "n2", "sender" : "n2"},
            {"n" : "n2", "sender" : "n3"},
            {"n" : "n3", "sender" : "n1"},
            {"n" : "n3", "sender" : "n2"},
            {"n" : "n3", "sender" : "n3"},
        ],
    },
    "__u8__" : {
        "functar" : functar_u8,
        "ground_truth" : ground_truth_u8,
        "action" : action_u8,
        "is_fair" : is_fair_u8,
        "is_guard" : is_guard_u8,
        "param_maps" : [
            {"dst" : "n1", "src" : "n1"},
            {"dst" : "n1", "src" : "n2"},
            {"dst" : "n1", "src" : "n3"},
            {"dst" : "n2", "src" : "n1"},
            {"dst" : "n2", "src" : "n2"},
            {"dst" : "n2", "src" : "n3"},
            {"dst" : "n3", "src" : "n1"},
            {"dst" : "n3", "src" : "n2"},
            {"dst" : "n3", "src" : "n3"},
        ],
    },
    "__u9__" : {
        "functar" : functar_u9,
        "ground_truth" : ground_truth_u9,
        "action" : action_u9,
        "is_fair" : is_fair_u9,
        "is_guard" : is_guard_u9,
        "param_maps" : [
            {"src" : "n1", "dst" : "n1"},
            {"src" : "n1", "dst" : "n2"},
            {"src" : "n1", "dst" : "n3"},
            {"src" : "n2", "dst" : "n1"},
            {"src" : "n2", "dst" : "n2"},
            {"src" : "n2", "dst" : "n3"},
            {"src" : "n3", "dst" : "n1"},
            {"src" : "n3", "dst" : "n2"},
            {"src" : "n3", "dst" : "n3"},
        ],
    },
    "__u10__" : {
        "functar" : functar_u10,
        "ground_truth" : ground_truth_u10,
        "action" : action_u10,
        "is_fair" : is_fair_u10,
        "is_guard" : is_guard_u10,
        "param_maps" : [
            {"n" : "n1", "sender" : "n1"},
            {"n" : "n1", "sender" : "n2"},
            {"n" : "n1", "sender" : "n3"},
            {"n" : "n2", "sender" : "n1"},
            {"n" : "n2", "sender" : "n2"},
            {"n" : "n2", "sender" : "n3"},
            {"n" : "n3", "sender" : "n1"},
            {"n" : "n3", "sender" : "n2"},
            {"n" : "n3", "sender" : "n3"},
        ],
    },
}


if __name__ == "__main__":
    from pprint import pprint
    import json
    grammars = {k : v["functar"][-1] for k, v in holes.items()}
    # pprint(grammars)
    # remove the typing info from the grammars
    for k, v in grammars.items():
        for i in range(len(v)):
            v[i] = [v[i][0], v[i][2]]
    print(json.dumps(grammars, indent=2))