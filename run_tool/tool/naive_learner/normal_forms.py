from pprint import pprint
import sympy
from sympy.core.symbol import Symbol 
from sympy.logic.boolalg import BooleanFalse, BooleanTrue

OPS = [
    "and", "or", "not", "set.union", "set.intersect", "set.minus", 
    "=", "<", "<="
]

def handle_and_edge_case(dnf):
    if isinstance(dnf, sympy.And):
        parity = {}
        for arg in dnf.args:
            lit = arg
            if arg.is_Atom:
                new_parity = True
            elif arg.is_Not:
                lit = arg.args[0]
                new_parity = False
            else:
                raise ValueError("Expected arg to be Atom or Not")
            if lit in parity and parity[lit] != new_parity:
                return sympy.false
            parity[lit] = new_parity
    return dnf

def is_normal_form(expr):
    if isinstance(expr, Symbol):
        return True
    if isinstance(expr, BooleanFalse):
        return True
    if isinstance(expr, BooleanTrue):
        return True
    if isinstance(expr, sympy.Or):
        return True
    if isinstance(expr, sympy.And):
        return True
    if isinstance(expr, sympy.Not):
        return True
    return False

def mk_atom_norm_aux(term):
    res = sympy.Symbol(str(term))
    assert isinstance(res, Symbol)
    return res

def mk_relation_symbol(relation, left, right):
    # Not: left/right can be either sexprs or sympy exprs
    return mk_atom_norm_aux([relation, left, right])

def mk_atom_norm(term):
    if isinstance(term, str):
        res = mk_atom_norm_aux(term)
    elif isinstance(term, tuple) and len(term) > 1 and term[1] == "emptyset":
        res = sympy.false
    elif isinstance(term, tuple) and len(term) > 1 and term[1] == True:
        res = sympy.true
    elif isinstance(term, tuple) and len(term) > 1 and term[1] == False:
        res = sympy.false
    elif isinstance(term, tuple):
        res = mk_atom_norm_aux(term)
    else:
        raise ValueError(f"Term {term} is not a string or a tuple")
    if not is_normal_form(res):
        raise ValueError(f"{res} is not in normal form")
    return res
    
def mk_list_atom_norm(head, tail):
    return mk_atom_norm_aux([head] + list(tail))

def mk_bool_norm(head, normal_tail):
    if head == "and":
        res = sympy.And(*normal_tail)
    elif head == "or":
        res = sympy.Or(*normal_tail)
    elif head == "not":
        res = sympy.Not(normal_tail[0])
    else:
        raise ValueError(f"Unknown head {head}")
    res = sympy.to_dnf(res, simplify=True)
    res = handle_and_edge_case(res)
    return res

def mk_set_norm(head, tail, normal_tail):
    if head == "set.union":
        res = sympy.Or(*normal_tail)
    elif head == "set.intersect":
        res = sympy.And(*normal_tail)
    elif head == "set.minus":
        res = sympy.And(normal_tail[0], sympy.Not(normal_tail[1]))
    else:
        raise ValueError(f"Unknown head {head}")
    res = sympy.to_dnf(res, simplify=True)
    res = handle_and_edge_case(res)
    # pprint(("SET_NORM", head, tail, res))
    # input("Press enter to continue...")
    return res

def mk_set_eq_norm(tail, normal_tail):
    left, right = normal_tail
    diff1 = mk_set_norm("set.minus", tail, [left, right])
    diff2 = mk_set_norm("set.minus", tail, [right, left])
    symm_diff = mk_set_norm("set.union", tail, [diff1, diff2])
    if isinstance(symm_diff, BooleanFalse):
        return sympy.true
    return mk_relation_symbol("=", sympy.false, symm_diff)

def mk_eq_norm(tail, normal_tail, tail_T):
    left, right = tail
    if left == right:
        return sympy.true
    left_int = (
        isinstance(left, tuple) 
        and left[0] == "Int" 
        and isinstance(left[1], int))
    right_int = (
        isinstance(right, tuple)
        and right[0] == "Int"
        and isinstance(right[1], int))
    if left_int and right_int:
        if left[1] == right[1]:
            return sympy.true
        return sympy.false
    if isinstance(tail_T, tuple) and tail_T[0] == "Set":
        return mk_set_eq_norm(tail, normal_tail)
    if str(left) < str(right):
        return mk_relation_symbol("=", left, right)
    return mk_relation_symbol("=", right, left)

def lt_norm(tail):
    left, right = tail
    if left == right:
        return sympy.false
    left_int = (
        isinstance(left, tuple) 
        and left[0] == "Int" 
        and isinstance(left[1], int))
    right_int = (
        isinstance(right, tuple)
        and right[0] == "Int"
        and isinstance(right[1], int))
    if left_int and right_int:
        if left[1] < right[1]:
            return sympy.true
        return sympy.false
    return mk_relation_symbol("<", left, right)

def lte_norm(tail):
    left, right = tail
    if left == right:
        return sympy.true
    left_int = (
        isinstance(left, tuple) 
        and left[0] == "Int" 
        and isinstance(left[1], int))
    right_int = (
        isinstance(right, tuple)
        and right[0] == "Int"
        and isinstance(right[1], int))
    if left_int and right_int:
        if left[1] <= right[1]:
            return sympy.true
    return mk_relation_symbol("<=", left, right)

def mk_norm(head, tail, normal_tail, T, tail_T):
    if tail is None:
        return mk_atom_norm(head)
    if normal_tail is None:
        raise ValueError("Normal tail is None, tail is not None")
    if tail_T is None:
        raise ValueError("Tail_T is None, tail is not None")
    if len(tail) != len(normal_tail):
        raise ValueError("Tail and normal_tail have different lengths")
    if len(tail) != len(tail_T):
        raise ValueError("Tail and tail_T have different lengths")
    for tail_expr in normal_tail:
        if not is_normal_form(tail_expr):
            raise ValueError(f"{tail_expr} is not in normal form")
    if head not in OPS:
        res = mk_list_atom_norm(head, tail)
    elif head in ["and", "or", "not"]:
        res = mk_bool_norm(head, normal_tail)
    elif head in ["set.union", "set.intersect", "set.minus"]:
        res = mk_set_norm(head, tail, normal_tail)
    elif head == "=":
        res = mk_eq_norm(tail, normal_tail, tail_T[0])
    elif head == "<":
        res = lt_norm(tail)
    elif head == "<=":
        res = lte_norm(tail)
    else:
        raise ValueError(f"Unknown head {head}")
    if not is_normal_form(res):
        raise ValueError(f"{res} is not in normal form")
    return res
