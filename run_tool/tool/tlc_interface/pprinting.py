'''This module's role is to convert the internal sexpr representation of an
expression into a string that can be plugged into a TLA+ sketch.
'''


def sexp_to_tla(sexp) -> str:
    if isinstance(sexp, list):
        head = sexp[0]
        tail = sexp[1:]
        if head == "set.singleton":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected singleton to have one argument, got {tail}")
            return f"{{{sexp_to_tla(tail[0])}}}"
        elif head == "set.union":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected union to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\cup {sexp_to_tla(tail[1])})"
        elif head == "set.intersect":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected intersect to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\cap {sexp_to_tla(tail[1])})"
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
        elif head == "set.minus":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected set difference to have two arguments,"
                    f" got {tail}")
            return f"({sexp_to_tla(tail[0])} \\ {sexp_to_tla(tail[1])})"
        elif head == "select":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected select to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])}[{sexp_to_tla(tail[1])}]"
        elif head == "store":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected store to have three arguments, got {tail}")
            array = sexp_to_tla(tail[0])
            key = sexp_to_tla(tail[1])
            value = sexp_to_tla(tail[2])
            return f"[{array} EXCEPT ![{key}] = {value}]"
        elif head == "+":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected addition to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} + {sexp_to_tla(tail[1])})"
        elif head == "*":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected multiplication to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} * {sexp_to_tla(tail[1])})"
        elif head == "=":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected equality to have two arguments, got {tail}")
            expr = f"({sexp_to_tla(tail[0])} = {sexp_to_tla(tail[1])})"
            return expr
        elif head == ">":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected greater than to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} > {sexp_to_tla(tail[1])})"
        elif head == "<":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected less than to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} < {sexp_to_tla(tail[1])})"
        elif head == ">=":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected greater or equal to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} >= {sexp_to_tla(tail[1])})"
        elif head == "<=":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected less or equal to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} <= {sexp_to_tla(tail[1])})"
        elif head == "powerset":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected powerset to have one argument, got {tail}")
            return f"SUBSET({sexp_to_tla(tail[0])})"
        elif head == "cardinality":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected cardinality to have one argument, got {tail}")
            return f"Cardinality({sexp_to_tla(tail[0])})"
        elif head == "comprehension":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected comprehension to have 3 arguments, got {tail}")
            var = tail[0]
            domain = tail[1]
            body = tail[2]
            return (
                f"{{ {var} \\in {sexp_to_tla(domain)} :"
                f" {sexp_to_tla(body)}}}")
        elif head == "forall":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected forall to have three arguments, got {tail}")
            var = tail[0]
            domain = tail[1]
            expr = tail[2]
            return f"\\A {var} \\in {sexp_to_tla(domain)} : {sexp_to_tla(expr)}"
        elif head == "exists":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected exists to have three arguments, got {tail}")
            var = tail[0]
            domain = tail[1]
            expr = tail[2]
            return f"\\E {var} \\in {sexp_to_tla(domain)} : {sexp_to_tla(expr)}"
        elif head == "and":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected and to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} /\\ {sexp_to_tla(tail[1])})"
        elif head == "or":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected or to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} \\/ {sexp_to_tla(tail[1])})"
        elif head == "not":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected not to have one argument, got {tail}")
            return f"~ ({sexp_to_tla(tail[0])})"
        elif head == "=>":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected implication to have two arguments, got {tail}")
            return f"({sexp_to_tla(tail[0])} => {sexp_to_tla(tail[1])})"
        elif head == "ite":
            if len(tail) != 3:
                raise ValueError(
                    f"Expected ite to have three arguments, got {tail}")
            return (
                f"IF {sexp_to_tla(tail[0])} THEN {sexp_to_tla(tail[1])}"
                f" ELSE {sexp_to_tla(tail[2])}")
        elif head == "seq.domain":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected seq.domain to have one argument, got {tail}")
            return f"DOMAIN({sexp_to_tla(tail[0])})"
        elif head == "seq.len":
            if len(tail) != 1:
                raise ValueError(
                    f"Expected seq.len to have one argument, got {tail}")
            return f"Len({sexp_to_tla(tail[0])})"
        elif head == "seq.at":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected seq.at to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])}[{sexp_to_tla(tail[1])}]"
        elif head == "tuple.at":
            if len(tail) != 2:
                raise ValueError(
                    f"Expected tuple.at to have two arguments, got {tail}")
            return f"{sexp_to_tla(tail[0])}[{sexp_to_tla(tail[1])}]"
        elif head == "tuple":
            return f"<<{', '.join([sexp_to_tla(x) for x in tail])}>>"
        elif head == "operator":
            ophead = tail[0]
            optail = tail[1:]
            return f"{ophead}({', '.join([sexp_to_tla(x) for x in optail])})"
        else:
            raise NotImplementedError(
                f"Unsupported operator encountered while"
                f" parsing sexp to tla: {head} applied to {tail}")
    elif sexp == ("Bool", True):
        return "TRUE"
    elif sexp == ("Bool", False):
        return "FALSE"
    elif isinstance(sexp, tuple) and len(sexp) > 1 and sexp[1] == "emptyset":
        return "{}"
    elif isinstance(sexp, tuple) and len(sexp) > 0:
        sort = sexp[0]
        if (
            not (sort == "Int" 
                or (isinstance(sort, tuple) and sort[0] == "Dom")
                or (isinstance(sort, tuple)))):
            raise NotImplementedError(
                f"Unsupported sexp encountered while parsing sexp to tla:"
                f" {sexp}")
        if len(sexp) != 2:
            raise ValueError(
                f"Expected integer to have one argument, got {sexp}")
        if isinstance(sexp[1], int):
            return str(sexp[1])
        elif sexp[1] is None:
            return "Nil"
        else:
            raise ValueError(
                f"Expected integer to have an integer argument or None,"
                f" got {sexp}")
    elif isinstance(sexp, str):
        return str(sexp)
    else:
        raise NotImplementedError(
            f"Unsupported sexp encountered while parsing sexp to tla: {sexp}")
