# -*- coding: utf-8 -*-
"""
Driver for the Paxos+OUM sketch — no mk_sketch helpers, just raw tables.
"""

from pathlib import Path

# 1) Read in the .tla and .cfg as strings
dir_path = Path(__file__).resolve().parent
PREFIX   = "paxos_oum_sketch"

sketch = open(dir_path / f"{PREFIX}.tla", "r").read()
config = open(dir_path / f"{PREFIX}.cfg", "r").read()

# 2) Candidate‐generation needs a constant map: each TLA+ CONSTANT → its domain
constants = [
    ("Value", ("Set", "Int")),
    ("Acceptor", ("Set", "Int")),
    ("Quorum",  ("Set", ("Set", "Int"))),
    ("ClientRequest", "Int"),
    ("MaxSeq", "Int"),
]

# 3) Any extra invariants/assumes for the learner? (none here)
assumes = [
    ["!=", "n1", "n2", "n3"],
    ["=",
        "Node",
        ["set.union",
          ["set.singleton", "n1"],
          ["set.singleton", "n2"],
          ["set.singleton", "n3"]
        ]
    ],
]

# 4) Action parameter lists for each action
act_params = {
    "Inital predicate": [],
    "Phase1a"   : ["b"],
    "Phase1b"   : ["a"],
    "Phase2a"   : ["b","v"],
    "Phase2b"   : ["a"],
    "Send"      : ["m"],
    "OUMSend"   : ["req"],
    "OUMDeliver": [],
}

# 5) Hole‐metadata: for each HOLE_<…> the learner needs
holes = {
  "HOLE_Ph1a": {
      "ground_truth":    "TRUE",
      "parsed_ground_truth": "TRUE",
      "functar":         ("HOLE_Ph1a", ["b"]),
      "is_guard":        True,
      "action":          "Phase1a",
      "param_maps":      {},      # no special maps
      "depends":         ["b"],
  },
  "HOLE_Ph1b": {
      "ground_truth":    "TRUE",
      "parsed_ground_truth": "TRUE",
      "functar":         ("HOLE_Ph1b", ["a"]),
      "is_guard":        True,
      "action":          "Phase1b",
      "param_maps":      {},
      "depends":         ["a"],
  },
  "HOLE_Ph2a": {
      "ground_truth":    "TRUE",
      "parsed_ground_truth": "TRUE",
      "functar":         ("HOLE_Ph2a", ["b","v"]),
      "is_guard":        True,
      "action":          "Phase2a",
      "param_maps":      {},
      "depends":         ["b","v"],
  },
  "HOLE_Ph2b": {
      "ground_truth":    "TRUE",
      "parsed_ground_truth": "TRUE",
      "functar":         ("HOLE_Ph2b", ["a"]),
      "is_guard":        True,
      "action":          "Phase2b",
      "param_maps":      {},
      "depends":         ["a"],
  },
}

# 6) Expose everything for main_paxos_oum.py
__all__ = [
    "sketch", "holes", "constants", "assumes", "act_params", "config"
]
