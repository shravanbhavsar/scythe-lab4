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

grammar_int_bal = [
    ["Start", "Int", [
        ("Int", -1),                    # constant –1
        ("Int", 0), ("Int", 1),         # small literals
        ["select", "maxBal", "a"],      # the usual guard  maxBal[a]
    ]]
]

# ---------------------------------------------------------------------------
#  6  Holes – now with 4‑field functars
# ---------------------------------------------------------------------------

holes = {
    "__hole1__": {
        # what TLC should see once the hole is filled
        "ground_truth":        "maxBal[a]",
        "parsed_ground_truth": "select(maxBal, a)",

        # 4‑tuple  <name, params, sort, grammar>
        "functar": [
            "__hole1__",               # operator name
            [["a", "Int"]],            # single formal parameter (acceptor id)
            "Int",                     # return sort
            grammar_int_bal            # grammar that builds Int terms
        ],

        "is_guard":  False,            # it’s an Int term, not Boolean guard
        "action":    "Phase2b",        # the action where it appears
        "param_maps": {},              # no special instantiations
        "depends":   ["a"],            # hole depends only on parameter a
    }
}

# ---------------------------------------------------------------------------
#  7  Public exports
# ---------------------------------------------------------------------------

__all__ = [
    "sketch", "config", "const", "assumes", "act_params", "holes",
]
