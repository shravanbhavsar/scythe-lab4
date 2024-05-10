'''This module's role is to convert the internal sexpr representation of an
expression into a string that can be plugged into a TLA+ skeleton.
'''

def get_powerset_arg(sexpr):
    head = sexpr[0]
    tail = sexpr[1:]
    if head != "set.filter":
        return None
    if len(tail) != 2:
        return None
    if len(tail[1]) != 2:
        return None
    if tail[1][0] != "universe":
        return None
    if len(tail[0]) != 3:
        return None
    if tail[0][0] != "lambda":
        return None
    lambda_args = tail[0][1]
    lambda_body = tail[0][2]
    if len(lambda_args) != 2:
        return None
    if lambda_args[0] != "variable_list":
        return None
    if len(lambda_body) != 3:
        return None
    if lambda_body[0] != "set.subset":
        return None
    return lambda_body[2]

def sexp_to_tla(sexp) -> str:
    if isinstance(sexp, list):
        head = sexp[0]
        tail = sexp[1:]
        powerset_arg = get_powerset_arg(sexp)
        if powerset_arg is not None:
            return f"SUBSET({sexp_to_tla(powerset_arg)})"
        elif head == "emptyset":
            return "{}"
        elif head == "set.filter":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected filter to have two arguments, got {tail}")
            body = sexp_to_tla(tail[0][-1])
            matrix = tail[0][1]
            v = matrix[-1][0]
            return f"{{{v} \\in {sexp_to_tla(tail[1])} : {body}}}"
        elif head == "set.card":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected cardinality to have one argument, got {tail}")
            return f"Cardinality({sexp_to_tla(tail[0])})"
        elif head == "set.singleton":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected singleton to have one argument, got {tail}")
            return f"{{{sexp_to_tla(tail[0])}}}"
        elif head == "set.union":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected union to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\cup {sexp_to_tla(tail[1])})"
        elif head == "set.member":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected member query to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\in {sexp_to_tla(tail[1])})"
        elif head == "set.subset":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected subset query to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\subseteq {sexp_to_tla(tail[1])})"
        elif head == "select":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected select to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])}[{sexp_to_tla(tail[1])}]"
        elif head == "store" and tail[0][0] == "store" and tail[0][1][0] == "store":
            # from pprint import pprint
            # pprint(sexp)
            kv1 = (tail[-2], tail[-1][-1])
            kv2 = (tail[0][-2], tail[0][-1][-1])
            kv3 = (tail[0][1][-2], tail[0][1][-1][-1])
            return str(dict([kv1, kv2, kv3]))
        elif head == "store":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected store to have three arguments, got {tail}")
            array = sexp_to_tla(tail[0])
            key = sexp_to_tla(tail[1])
            value = sexp_to_tla(tail[2])
            return f"[{array} EXCEPT ![{key}] = {value}]"
        elif head == "*":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected multiplication to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])} * {sexp_to_tla(tail[1])}"
        elif head == "=":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected equality to have two arguments, got {tail}")
            expr = f"{sexp_to_tla(tail[0])} = {sexp_to_tla(tail[1])}"
            return expr
        elif head == ">":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected greater than to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])} > {sexp_to_tla(tail[1])}"
        elif head in ["exists", "forall"]:
            '''In cvc5, quantifiers do not need to quantify over a particular 
            set. In tla, they do. This means that the cvc5 term is going to have
            just two arguments (the variable and the body), while the tla term
            will have three (the variable, the set, and the body). This function
            is responsible for teasing apart the cvc5 term and constructing the
            tla term.
            '''
            if len(tail) != 2:
                raise ValueError(
                    f"Expected quantifier to have two arguments, got {tail}")
            args = tail[0]
            body = tail[1]
            if len(args) != 2:
                raise ValueError(
                    f"Multi-variable quantifiers not supported, use nesting:"
                    f" got {args}")
            if len(args[1]) != 2:
                raise ValueError(
                    f"Expected variable to have two positions, got {args[1]}")
            arg_var = args[1][0]
            if len(body) != 3:
                raise ValueError(
                    f"Expected exists body to have three arguments,"
                    f" got {body}")
            
            # Quantifier specific checks and processing
            if head == "exists":
                quantifier = "\\E"
                if body[0] != "and":
                    raise ValueError(
                        f"Expected first term of exists body to be an and,"
                        f" got {body}")
            else:
                quantifier = "\\A"
                if body[0] != "=>":
                    raise ValueError(
                        f"Expected first term of forall body to be an"
                        f" implication, got {body}")
            
            in_matrix = body[1]
            body = body[2]
            if len(in_matrix) != 3:
                raise ValueError(
                    f"Expected in matrix to have three arguments,"
                    f" got {in_matrix}")
            if in_matrix[0] != "set.member":
                raise ValueError(
                    f"Expected first term of in matrix to be a member"
                    f" query, got {in_matrix}")
            if in_matrix[1] != arg_var:
                raise ValueError(
                    f"Expected variable in member query to be {arg_var},"
                    f" got {in_matrix}")
            domain = in_matrix[2]

            return (
                f"{quantifier} {arg_var} \\in {sexp_to_tla(domain)}"
                f" : {sexp_to_tla(body)}")
        elif head == "and":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected and to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} /\\ {sexp_to_tla(tail[1])})"
        elif head == "or":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected and to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\/ {sexp_to_tla(tail[1])})"
        elif head == "not":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected not to have one argument, got {tail}")
            return f"~ ({sexp_to_tla(tail[0])})"
        elif head.startswith("__"):
            return f"{head}({', '.join([sexp_to_tla(x) for x in tail])})"
            # return f"{head}(...)"
        else:
            raise NotImplementedError(
                f"Unsupported operator encountered while"
                f" parsing sexp to tla: {head} applied to {tail}")
    elif sexp == ("Bool", True):
        return "TRUE"
    elif sexp == ("Bool", False):
        return "FALSE"
    elif isinstance(sexp, tuple) and len(sexp) > 0 and sexp[0] == "Int":
        assert(len(sexp) == 2 and isinstance(sexp[1], int))
        return str(sexp[1])
    elif isinstance(sexp, str):
        return str(sexp)
    else:
        raise NotImplementedError(
            f"Unsupported sexp encountered while parsing sexp to tla: {sexp}")
