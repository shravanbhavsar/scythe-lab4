'''This is the module where benchmark specific operators are defined.
'''

# TODO: Allow the user to supply an operator table as an input to the synthesis
# tool, rather than defining their operators in this table. 

# TODO: Operator tables should be benchmark specific, rather than having one
# table.

import itertools

def eval_Quorums(py_set):
    return [
        set(x) for x in itertools.chain.from_iterable([
            x for x in [
                itertools.combinations(py_set, i) 
                for i in range(len(py_set) + 1)]])
        if len(x) > len(py_set) // 2]

OPERATOR_TABLE = {
    "Quorums": (eval_Quorums, 1),
}