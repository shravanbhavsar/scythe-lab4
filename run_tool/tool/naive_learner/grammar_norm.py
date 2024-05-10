from pprint import pprint


def expr_terminals(expr, nts):
    if isinstance(expr, str):
        if expr not in nts:
            return {expr}
        else:
            return set()
    elif isinstance(expr, list):
        if expr[0] == "emptyset":
            if len(expr) != 2:
                raise ValueError("Expected list of length 2")
            return {("emptyset", expr[1])}
        res = set()
        for subexpr in expr[1:]:
            res |= expr_terminals(subexpr, nts)
        return res
    elif isinstance(expr, tuple):
        # print("EXPRESSION", expr)
        if len(expr) != 2:
            raise ValueError(f"Expected tuple of length 2, got {expr}")
        sort, val = expr
        allowed = {
            "Int",
            "Bool", 
            ("Set", ("Tuple", "Int", "Int")),
            ("Set", "Int"),
        }
        allowed_fn = (
            lambda x: (
                x in allowed 
                or (isinstance(x, tuple) and x[0] == "Dom")
                or (isinstance(x, tuple) 
                    and x[0] == "Set"
                    and isinstance(x[1], tuple) 
                    and x[1][0] == "Dom")))
        if not isinstance(sort, tuple) and not isinstance(sort, str):
            raise ValueError(f"Expected tuple, got {sort}")
        if not allowed_fn(sort):
            raise ValueError(
                f"Expected Dom sort or sort in {allowed}, got {sort}")
        if sort[0] == "Set" and val != "emptyset":
            raise ValueError(f"Expected emptyset, got {val}")
        return {expr}
    else:
        raise NotImplementedError(f"expr_terminals not implemented for {expr}")

def grammar_terminals(grammar, nts):
    res = set()
    for production in grammar:
        for rule in production[2]:
            res |= expr_terminals(rule, nts)
    return res

def rule_is_normal(rule, nts, ts):
    if isinstance(rule, str) or isinstance(rule, tuple):
        if rule in nts:
            return False
        if rule not in ts:
            raise ValueError(f"Expected {rule} in terminal symbols.")
        return True
    elif isinstance(rule, list):
        tail = rule[1:]
        if any(isinstance(arg, list) for arg in tail):
            return False
        return all(arg in nts for arg in tail)
    else:
        raise ValueError(f"Expected string or list, got {rule}")

def production_is_normal(production, nts, ts):
    _, _, rules = production
    return all(rule_is_normal(rule, nts, ts) for rule in rules)

def grammar_is_normal(grammar, nts, ts):
    return all(
        production_is_normal(production, nts, ts) 
        for production in grammar)

def one_step_normalize_grammar(grammar, nts, ts, i):
    new_grammar = []
    new_nts = set()
    for production in grammar:
        if production_is_normal(production, nts, ts):
            new_grammar.append(production)
            continue
        new_rules = []
        nt, sort, rules = production
        for rule in rules:
            if rule_is_normal(rule, nts, ts):
                new_rules.append(rule)
                continue
            if isinstance(rule, str) and rule in nts:
                if rule != nt:
                    others_productions = [
                        production 
                        for production in grammar if production[0] == rule]
                    for other_production in others_productions:
                        _, _, other_rules = other_production
                        new_rules += other_rules
                continue
            head = rule[0]
            tail = rule[1:]
            new_tail = []
            for arg in tail:
                if arg in nts:
                    new_tail.append(arg)
                else:
                    new_nt = f"__NT{i}"
                    new_nts.add(new_nt)
                    i += 1
                    new_tail.append(new_nt)
                    new_production = [new_nt, "", [arg]]
                    new_grammar.append(new_production)
            new_rule = [head] + new_tail
            new_rules.append(new_rule)
        new_production = [nt, sort, new_rules]
        new_grammar.append(new_production)
    return i, new_grammar, new_nts

def normalize_grammar_rec(grammar, nts, ts, i):
    if grammar_is_normal(grammar, nts, ts):
        return grammar
    # print()
    # print("normalize_grammar_rec pre one step GRAMMAR", grammar[0])
    j, new_grammar, new_nts = one_step_normalize_grammar(grammar, nts, ts, i)
    # print("normalize_grammar_rec post one step GRAMMAR", new_grammar[0])
    return normalize_grammar_rec(new_grammar, nts + list(new_nts), ts, j)

def validate_grammar(grammar):
    for production in grammar:
        if len(production) != 3:
            raise ValueError(
                "Expected production of length 3. Got:", production)
        nt, t, rules = production
        # pprint(production)
        if not isinstance(nt, str):
            raise ValueError(f"Expected string, got {nt}")
        if not isinstance(t, str) and not isinstance(t, tuple):
            raise ValueError(f"Expected string or tuple, got {t}")
        if not isinstance(rules, list):
            raise ValueError(f"Expected list, got {rules}")


def rotate_start_nt(grammar, start_nt):
    '''This function rotates the start non-terminal to the start of the
    grammar.
    '''
    head = [production for production in grammar if production[0] == start_nt]
    assert len(head) == 1, f"Expected one production for {start_nt}, got {head}"
    head = head[0]
    tail = [production for production in grammar if production[0] != start_nt]
    return [head] + tail

def normalize_grammar(grammar_raw, start_nt):
    validate_grammar(grammar_raw)
    nts = [nt for nt, _, _ in grammar_raw]
    ts = grammar_terminals(grammar_raw,nts)
    # print()
    # print("normalize_grammar pre rec GRAMMAR", grammar_raw[0])
    new_grammar = normalize_grammar_rec(grammar_raw, nts, ts, 0)
    # print("normalize_grammar post rec GRAMMAR", new_grammar[0])
    new_grammar = rotate_start_nt(new_grammar, start_nt)
    return new_grammar
