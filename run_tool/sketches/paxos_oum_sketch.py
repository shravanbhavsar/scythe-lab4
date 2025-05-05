# -*- coding: utf-8 -*-
"""
Refactored Paxos‑OUM sketch description (v2)
⇒ Each *functar* entry now contains the full 4‑tuple
   ⟨name, param‑list‑with‑sorts, return‑sort, grammar⟩
   so the naive_learner can safely index `f[3]`.
"""

from pathlib import Path

# ---------------------------------------------------------------------------
#  1  Read the TLA⁺ module and its .cfg file
# ---------------------------------------------------------------------------

dir_path = Path(__file__).parent.absolute()

sketch  = (dir_path / "paxos_oum_sketch.tla").read_text()
config  = (dir_path / "paxos_oum_sketch.cfg").read_text()

# ---------------------------------------------------------------------------
#  2  Constant declarations (→ `const`)
# ---------------------------------------------------------------------------

constants = [
    ("n1", "Int"), ("n2", "Int"), ("n3", "Int"),
    ("Value", ("Set", "Int")),
    ("Acceptor", ("Set", "Int")),
    ("Quorum", ("Set", ("Set", "Int"))),
    ("ClientRequest", "Int"),
    ("MaxSeq", "Int"),
]

# ---------------------------------------------------------------------------
#  3  Global assumptions
# ---------------------------------------------------------------------------

assumes = [
    ["!=", "n1", "n2", "n3"],
    ["=", "Node", [
        "set.union",
        ["set.singleton", "n1"], ["set.singleton", "n2"], ["set.singleton", "n3"]
    ]],
]

# ---------------------------------------------------------------------------
#  4  Action → parameter mapping
# ---------------------------------------------------------------------------

act_params = {
    "Initial predicate": [],
    "Phase1a": ["b"],
    "Phase1b": ["a"],
    "Phase2a": ["b", "v"],
    "Phase2b": ["a"],
    "Send":       ["m"],
    "OUMSend":    ["req"],
    "OUMDeliver": [],
}

# ---------------------------------------------------------------------------
#  5  Simple Boolean grammar shared by all guard holes
# ---------------------------------------------------------------------------

grammar_bool_true = [
    ["Start", "Bool", [  # non‑terminal Start of sort Bool
        ("Bool", True),   # constant TRUE
        ("Bool", False)   # constant FALSE  (included for completeness)
    ]]
]

# ---------------------------------------------------------------------------
#  6  Holes – now with 4‑field functars
# ---------------------------------------------------------------------------

holes = {
    "__hole1__": {
        "ground_truth":        "TRUE",
        "parsed_ground_truth": "TRUE",
        "functar": [
            "__hole1__",          # (0) function name
            [["b", "Int"]],       # (1) parameter list with sorts
            "Bool",               # (2) return sort
            grammar_bool_true      # (3) grammar
        ],
        "is_guard":  True,
        "action":    "Phase1a",
        "param_maps": {},
        "depends":   ["b"],
    },
    "HOLE_Ph1b": {
        "ground_truth":        "TRUE",
        "parsed_ground_truth": "TRUE",
        "functar": [
            "HOLE_Ph1b",
            [["a", "Int"]],
            "Bool",
            grammar_bool_true
        ],
        "is_guard":  True,
        "action":    "Phase1b",
        "param_maps": {},
        "depends":   ["a"],
    },
    "HOLE_Ph2a": {
        "ground_truth":        "TRUE",
        "parsed_ground_truth": "TRUE",
        "functar": [
            "HOLE_Ph2a",
            [["b", "Int"], ["v", "Int"]],
            "Bool",
            grammar_bool_true
        ],
        "is_guard":  True,
        "action":    "Phase2a",
        "param_maps": {},
        "depends":   ["b", "v"],
    },
    "HOLE_Ph2b": {
        "ground_truth":        "TRUE",
        "parsed_ground_truth": "TRUE",
        "functar": [
            "HOLE_Ph2b",
            [["a", "Int"]],
            "Bool",
            grammar_bool_true
        ],
        "is_guard":  True,
        "action":    "Phase2b",
        "param_maps": {},
        "depends":   ["a"],
    },
}

# ---------------------------------------------------------------------------
#  7  Public exports
# ---------------------------------------------------------------------------

__all__ = [
    "sketch", "config", "const", "assumes", "act_params", "holes",
]
