def size_fn(expr):
    if isinstance(expr, list):
        return 1 + sum(size_fn(arg) for arg in expr[1:])
    else:
        return 1

def expr_lt(expr1, expr2):
    if size_fn(expr1) < size_fn(expr2):
        return True
    if not isinstance(expr1, list) and isinstance(expr2, list):
        return str(expr1) < str(expr2)
    if isinstance(expr1, list) and not isinstance(expr2, list):
        return False
    if not isinstance(expr1, list) and isinstance(expr2, list):
        return True
    if len(expr1) < len(expr2):
        return True
    if len(expr1) > len(expr2):
        return False
    head1 = expr1[0]
    head2 = expr2[0]
    if head1 < head2:
        return True
    if head1 > head2:
        return False
    tail1 = expr1[1:]
    tail2 = expr2[1:]
    for t1, t2 in zip(tail1, tail2):
        if expr_lt(t1, t2):
            return True
        if expr_lt(t2, t1):
            return False
    # The expression trees are equal
    return False

def is_ordered(exprs):
    for i in range(len(exprs) - 1):
        if not expr_lt(exprs[i], exprs[i + 1]):
            return False
    return True

# Silly inserted sort, probably fine since lists should be small
def mk_ordered(exprs):
    new_exprs = []
    for expr in exprs:
        added = False
        for expr2 in new_exprs:
            if expr_lt(expr, expr2):
                new_exprs.insert(new_exprs.index(expr2), expr)
                added = True
                break
        if not added:
            new_exprs.append(expr)
    assert is_ordered(new_exprs)
    return new_exprs