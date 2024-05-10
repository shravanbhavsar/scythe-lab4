'''This module uses BFS to enumerate all possible elements of a grammar.
'''

import itertools
from math import prod as math_prod
import math
from pprint import pprint

from .dovetail import IndexedGenerator

from .expr_helpers import is_ordered, mk_ordered, size_fn


from .normal_forms import mk_norm

try:
    from .grammar_norm import rotate_start_nt
    from .grammar_norm import grammar_terminals, normalize_grammar
    from .dovetail import lattice_slices, smart_lattice_slices
    from .dovetail import smarter_lattice_slices
    from .dovetail import commutable_product
except ImportError:
    from grammar_norm import rotate_start_nt
    from grammar_norm import grammar_terminals, normalize_grammar
    from dovetail import lattice_slices, smart_lattice_slices
    from dovetail import smarter_lattice_slices
    from dovetail import commutable_product


def nested_list_to_nested_tuple(nested_list):
    if isinstance(nested_list, list) or isinstance(nested_list, tuple):
        res = tuple(nested_list_to_nested_tuple(arg) for arg in nested_list)
    else:
        res = nested_list
    try:
        hash(res)
    except TypeError:
        raise ValueError(f"Expected hashable, got {res}")
    return res

def untuple(candidate, ts):
    if candidate in ts:
        return candidate
    elif isinstance(candidate, tuple):
        if len(candidate) < 2:
            raise ValueError(f"Expected tuple of length >= 2, got {candidate}")
        head = candidate[0]
        if not isinstance(head, str):
            raise ValueError(f"Expected string, got {head}")
        tail = candidate[1:]
        return [head] + list(untuple(arg, ts) for arg in tail)
    else:
        raise ValueError(f"Expected tuple or string, got {candidate}")

def nt_free(candidate, nts, ts):
    if candidate in ts:
        return True
    elif candidate in nts:
        return False
    elif isinstance(candidate, tuple):
        return all(nt_free(arg, nts, ts) for arg in candidate[1:])

def depth1_nt(grammar, nt):
    for fnt, _, rules in grammar:
        if fnt == nt:
            for rule in rules:
                yield rule

def typed_depth1_nt(grammar, nt):
    for fnt, ty, rules in grammar:
        if fnt == nt:
            for rule in rules:
                yield rule, ty

def mk_extension(candidate, grammar, nts, ts):
    '''Let n1, n2, ..., nk be the non-terminal symbols in candidate,
    including repeated symbols. Let P1, P2, ..., Pk be the possible
    productions for each ni. This function returns all expressions
    obtained by replacing ni with Pj for all i and j.
    '''
    if candidate in ts:
        return [candidate]
    elif candidate in nts:
        d = depth1_nt(grammar, candidate)
        return list(d)
    elif isinstance(candidate, tuple):
        head, tail = candidate[0], candidate[1:]
        tail_extensions = [mk_extension(arg, grammar, nts, ts) for arg in tail]
        return [
            tuple([head] + list(tail_extension))
            for tail_extension in itertools.product(*tail_extensions)]
    else:
        raise ValueError(f"Expected tuple or string, got {candidate}")

def enumerate_grammar_memo_rec_unopt(
        grammar, nts, ts, start_nt, size, gram_id, memo):
    '''Handles the recursive case of enumerate_grammar_memo.
    '''
    for rule in depth1_nt(grammar, start_nt):
        if not isinstance(rule, list):
            continue
        # print("memo_rec RULE", rule)
        head = rule[0]
        tail = rule[1:]
        for slice in lattice_slices(len(tail), size-1):
            # print("SLICE", slice)
            if any(x == 0 for x in slice):
                continue
            zs = zip(tail, slice)
            tail_exprs = [
                enumerate_grammar_memo_unopt(
                    grammar, nts, ts, arg, s, gram_id) for arg, s in zs]
            for tail_expr in itertools.product(*tail_exprs):
                expr = [head] + list(tail_expr)
                memo[(gram_id, start_nt, size)].append(expr)
                yield expr

def get_nt_T(nt, grammar):
    for fnt, ty, _ in grammar:
        if fnt == nt:
            return ty
    raise ValueError(f"Expected nt in grammar, got {nt}")

def enumerate_grammar_memo_rec(
        grammar, nts, ts, start_nt, size, gram_id, local_memo, memo, 
        nf_forward, nf_backward, debugging=None):
    '''Handles the recursive case of enumerate_grammar_memo.
    - nf_forward maps an expression to its normal form
    - nf_backward maps a normal form to the first expression encountered that
      has that normal form.
    '''

    wrap_key = lambda nt, x: (gram_id, nt, x)
    wrap_norm_key = lambda nt, x: wrap_key(nt, str(x))
    memo_key = wrap_key(start_nt, size)

    for rule, T in typed_depth1_nt(grammar, start_nt):
        if not isinstance(rule, list):
            continue
        # print("memo_rec RULE", rule)
        head = rule[0]
        tail = rule[1:]
        tail_Ts = [get_nt_T(nt, grammar) for nt in tail]
        for slice in lattice_slices(len(tail), size-1):
            if (
                    head in ["set.union", "set.intersect", "="]
                    and tail[0] == tail[1]
                    and len(slice) >= 2
                    and slice[0] > slice[1]): # type: ignore
                break
            if debugging:
                print("SLICE", slice)
            if any(x == 0 for x in slice):
                continue

            zs = list(zip(tail, slice))
            tail_exprs = [
                enumerate_grammar_memo(
                    grammar, nts, ts, arg, s, gram_id) for arg, s in zs]
            if (
                    head in ["set.union", "set.intersect", "="]
                    and tail[0] == tail[1]
                    and len(slice) >= 2
                    and slice[0] == slice[1]): # type: ignore
                # tail_product = commutable_product(tail_exprs)
                tail_product = itertools.product(*tail_exprs)
            else:
                tail_product = itertools.product(*tail_exprs)
            for tail_expr in tail_product:
                expr = [head] + list(tail_expr)
                if debugging:
                    print("EXPR", expr)
                zipped_tail = list(zip(tail, tail_expr))
                # This is necessary since set_norm assumes the elements of tail
                # are already in normal form.
                if any(
                        wrap_norm_key(nt, arg) not in nf_forward 
                        for nt, arg in zipped_tail):
                    raise RuntimeError(
                        "Expected normal form of subexpression in cache."
                        f"\nCache: {nf_forward}"
                        f"\nMissing: {[(nt, arg) for nt, arg in zipped_tail if wrap_norm_key(nt, arg) not in nf_forward]}")
                normal_tail = [
                    nf_forward[
                        wrap_norm_key(nt, arg)] for nt, arg in zipped_tail]
                # NOTE: nf_forward should consider tail_Ts, since equality
                # between sets and equality between bools uses the same
                # representation.
                normal_form = mk_norm(head, tail_expr, normal_tail, T, tail_Ts)
                # print("NF", expr, normal_form)
                # if isinstance(T, tuple) and T[0] == "Set":
                #     normal_form = set_norm(near_normal_form, T)
                # elif T == "Bool":
                #     normal_form = bool_norm(near_normal_form, tail_Ts)
                # elif head in ["="]:
                #     assert tail_Ts[0] == tail_Ts[1]
                #     normal_form = eq_norm(near_normal_form, tail_Ts[0])
                # elif head in ["<"]:
                #     assert tail_Ts[0] == tail_Ts[1]
                #     normal_form = lt_norm(near_normal_form, tail_Ts[0])
                # elif head in ["<="]:
                #     assert tail_Ts[0] == tail_Ts[1]
                #     normal_form = lte_norm(near_normal_form, tail_Ts[0])
                fw_key = wrap_norm_key(start_nt, expr)
                bw_key = wrap_norm_key(start_nt, normal_form)
                if bw_key in nf_backward:
                    new_expr = nf_backward[bw_key]
                else:
                    nf_forward[fw_key] = normal_form
                    nf_backward[bw_key] = expr
                    new_expr = expr

                new_size = size_fn(new_expr)
                inner_key = wrap_key(start_nt, new_size)
                if (
                        new_size < size 
                        and inner_key in memo 
                        and new_expr in memo[inner_key]):
                    continue
                if (
                        new_size == size
                        and inner_key in local_memo 
                        and new_expr in local_memo[inner_key]):
                    continue
                if new_size < size:
                    raise RuntimeError(
                        f"Normal form of smaller size not encountered before."
                        f" We disallow this to avoid missing expressions."
                        f"\nold size: {size}, new size: {new_size}"
                        f"\nold expr: {expr}, new expr: {new_expr}"
                    )
                if inner_key not in memo:
                    memo[inner_key] = []
                if inner_key not in local_memo:
                    local_memo[inner_key] = [] 
                local_memo[inner_key].append(new_expr)
                if new_expr not in memo[inner_key]:
                    memo[inner_key].append(new_expr)
                yield new_expr

def enumerate_grammar_memo_unopt(
        grammar, nts, ts, start_nt, size, gram_id, 
        memo={}, done=set()):
    '''This function returns a generator that yields all possible expressions
    size=size from the grammar for the non-terminal start_nt. Note that this
    returns expressions of exactly size=size, not smaller. Refer to size(expr)
    for the definition of size.
    '''
    memo_key = (gram_id, start_nt, size)
    if memo_key not in memo:
        memo[memo_key] = []
    elif memo_key in done:
        for expr in memo[memo_key]:
            yield expr
        return
    grammar = rotate_start_nt(grammar, start_nt)
    rules = depth1_nt(grammar, start_nt)
    if size == 1:
        G = (x for x in rules)
        rule = next(G, None)
        while rule is not None:
            nxt_rule = next(G, None)
            if nxt_rule is None:
                done.add(memo_key)
            if not isinstance(rule, list) and rule in ts:
                memo[memo_key].append(rule)
                yield rule
            rule = nxt_rule
    else:
        G = enumerate_grammar_memo_rec_unopt(
            grammar, nts, ts, start_nt, size, gram_id, memo)
        expr = next(G, None)
        while expr is not None:
            nxt_expr = next(G, None)
            if nxt_expr is None:
                done.add(memo_key)
            yield expr
            expr = nxt_expr
    done.add(memo_key)

def enumerate_grammar_memo(
        grammar, nts, ts, start_nt, size, gram_id, 
        memo={}, done=set(), nf_forward={}, nf_backward={}, 
        debugging=None
        ):
    '''This function returns a generator that yields all possible expressions
    size=size from the grammar for the non-terminal start_nt. Note that this
    returns expressions of exactly size=size, not smaller. Refer to size(expr)
    for the definition of size.
    '''
    wrap_key = lambda x: (gram_id, start_nt, x)
    wrap_norm_key = lambda x: wrap_key(str(x))
    # memo_key = (gram_id, start_nt, size)
    memo_key = wrap_key(size)
    # local memo is not shared between generators with the same args. This is
    # critical for completeness. Otherwise a generator might incorrectly believe
    # that it has yielded something that it has not.
    local_memo = dict()
    local_memo[memo_key] = []
    if memo_key not in memo:
        memo[memo_key] = []
        if debugging:
            print("memo_key not in memo", memo_key)
    # elif memo_key in done:
    else:
        # re-yield everything in the memo
        if debugging:
            print("memo_key in done", memo_key)
        for expr in memo[memo_key]:
            if debugging:
                print("memo expr", expr)
            local_memo[memo_key].append(expr)
            yield expr
        # Extend the memo if the prior generator didn't exhaust the grammar
        if memo_key in done:
            return
    if debugging:
        print("memo_key not in done", memo_key)
        pprint(memo[memo_key])
    grammar = rotate_start_nt(grammar, start_nt)
    rules = depth1_nt(grammar, start_nt)
    if size == 1:
        exprs = []
        for rule in rules:
            if not isinstance(rule, list) and rule in ts:
                exprs.append(rule)
        # exprs = mk_ordered(exprs)
        for expr in exprs:
            T = get_nt_T(start_nt, grammar)
            normal_form = mk_norm(expr, None, None, T, None)
            # if isinstance(T, tuple) and T[0] == "Set":
            #     normal_form = set_norm(expr, T)
            # if T == "Bool":
            #     normal_form = bool_norm(expr, None)
            # print("NORM", expr, normal_form)
            fw_key = wrap_norm_key(expr)
            bw_key = wrap_norm_key(normal_form)
            nf_forward[fw_key] = normal_form
            nf_backward[bw_key] = expr
            # print("NF", expr, normal_form)
            if expr not in memo[memo_key]:
                memo[memo_key].append(expr)
            if expr not in local_memo[memo_key]:
                local_memo[memo_key].append(expr)
                yield expr
    else:
        G = enumerate_grammar_memo_rec(
            grammar, nts, ts, start_nt, size, gram_id, 
            local_memo=local_memo, memo=memo, 
            nf_forward=nf_forward, nf_backward=nf_backward, debugging=debugging)
        expr = next(G, None)
        if debugging:
            print("expr", expr)
        while expr is not None:
            nxt_expr = next(G, None)
            if debugging:
                print("expr", expr)
            if nxt_expr is None:
                done.add(memo_key)
            # local_memo[memo_key].append(expr)
            yield expr
            expr = nxt_expr
    done.add(memo_key)

def enumerate_grammars_aux_unopt(grammars, ntss, tss, grammar_ids):
    start_nts = [g[0][0] for g in grammars]
    # zs = zip(grammars, ntss, tss, start_nts, grammar_ids)
    size = len(grammars)
    # max_cnt = math.prod(lang_size_grammar(g) for g in grammars)
    # cnt = 0
    while True:
        for slice in lattice_slices(len(grammars), size):
            # print("SLICE", slice)
            if any(x == 0 for x in slice):
                continue
            zs = zip(grammars, ntss, tss, start_nts, slice, grammar_ids)
            Gs = [
                enumerate_grammar_memo_unopt(*z) for z in zs] # type: ignore
            for exprs in itertools.product(*Gs):
                # cnt += 1
                yield exprs
                # if cnt >= max_cnt:
                #     return
        size += 1

def mk_smart_slicing_pools_not_good_enough(grammars, size):
    # TODO: compute min sizes based on smallest expression in each grammar
    per_grammar_min_sizes = tuple(1 for _ in grammars)
    per_grammar_max_sizes = [
        size - sum(per_grammar_min_sizes) + min_size 
        for min_size in per_grammar_min_sizes]
    bounds = list(zip(per_grammar_min_sizes, per_grammar_max_sizes))
    pools = [
        frozenset(range(min_, max_ + 1)) 
        for min_, max_ in bounds]
    # TODO: determine for each size in each pool whether the grammar has an
    # expression of that size. Filter out sizes that are not attainable.
    return pools

def mk_smart_slicing_pools(size, zs):
    # First we compute the size of the smallest expression in each grammar
    smallest_expression_sizes = []
    # preliminary_max = size - len(zs) + 1
    preliminary_max = size
    # print("initial preliminary_max", preliminary_max)
    for idx, z in enumerate(zs):
        # print("idx smart slicing pools", idx, size)
        smallest_expression = None
        smallest_expression_size = None
        for inner_size in range(1, preliminary_max+1):
            grammar, nts, ts, start_nt, grammar_id = z
            newz = (grammar, nts, ts, start_nt, inner_size, grammar_id)
            G = enumerate_grammar_memo(*newz)
            expr = next(G, None)
            if expr is not None:
                smallest_expression = expr
                smallest_expression_size = inner_size
                break
        if smallest_expression is None:
            return None
        # print("idx expr preliminary_max", idx, expr, preliminary_max)
        preliminary_max -= smallest_expression_size
        smallest_expression_sizes.append(smallest_expression_size)
    # Now we compute per grammar max sizes
    per_grammar_max_sizes = [
        size - sum(smallest_expression_sizes) + min_size 
        for min_size in smallest_expression_sizes]
    # Now we compute the pools
    pools = [
        frozenset(range(min_, max_ + 1)) 
        for min_, max_ in zip(smallest_expression_sizes, per_grammar_max_sizes)]
    # TODO: determine for each size in each pool whether the grammar has an
    # expression of that size. Filter out sizes that are not attainable.
    return pools

def enumerate_grammars_aux_smart(grammars, ntss, tss, grammar_ids):
    start_nts = [g[0][0] for g in grammars]
    # zs = zip(grammars, ntss, tss, start_nts, grammar_ids)
    size = len(grammars)
    max_cnt = math.prod(lang_size_grammar(g) for g in grammars)
    cnt = 0
    while True:
        pool_zs = list(zip(grammars, ntss, tss, start_nts, grammar_ids))
        pools = mk_smart_slicing_pools(size, pool_zs)
        if pools is None:
            size += 1 #WARNING WARNING WARNING WARNING WARNING WARNING
            continue
        # print("size", size)
        for slice in smart_lattice_slices(pools, size):
            # print("SLICE", slice)
            if any(x == 0 for x in slice):
                continue
            zs = list(zip(grammars, ntss, tss, start_nts, slice, grammar_ids))
            Gs = [
                enumerate_grammar_memo(*z, debugging=None) 
                for z in zs]            
            for exprs in itertools.product(*Gs):
                cnt += 1
                yield exprs
                if cnt >= max_cnt:
                    return
        size += 1 #WARNING WARNING WARNING WARNING WARNING WARNING

def mk_smarter_slicing_pools(size, zs):
    grammars, ntss, tss, start_nts, grammar_ids, hole_infos = zip(*zs)
    inner_zs = list(zip(grammars, ntss, tss, start_nts, grammar_ids))
    pools = mk_smart_slicing_pools(size, inner_zs)
    if pools is None:
        return None
    bs = []
    for hole_info1, hole_info2 in zip(hole_infos, hole_infos[1:]):
        if (
                hole_info1["is_guard"] 
                and hole_info2["is_guard"] 
                and hole_info1["action"] == hole_info2["action"]):
            bs.append(True)
        else:
            bs.append(False) 
    bs.append(False)
    if len(bs) != len(pools):
        raise RuntimeError(f"Expected len(bs) == len(pools), got {bs, pools}")
    return list(zip(bs, pools))

def commutable_product_by_size(idxGs):
    G = IndexedGenerator(idxGs[0][1])
    def inner_G():
        jdx = 0
        while True:
            nxt = G[jdx]
            if nxt is None:
                break
            yield nxt
            jdx += 1
    idxs = [idx for idx, G in idxGs]
    inner_Gs = [inner_G() for _ in idxGs]
    for x in commutable_product(inner_Gs):
        yield list(zip(idxs, x))

def commutable_product_by_group(Gs):
    by_slices = dict()
    for idx, (G, sz) in Gs:
        if sz not in by_slices:
            by_slices[sz] = []
        by_slices[sz].append((idx, G))
    inner_Gs = []
    for sz, idxGs in by_slices.items():
        inner_G = commutable_product_by_size(idxGs)
        inner_Gs.append(inner_G)
    for x in itertools.product(*inner_Gs):
        aux = itertools.chain(*x)
        aux = sorted(aux, key=lambda x: x[0])
        aux = [x[1] for x in aux]
        yield aux

def commutable_product_by_groups(Gs, slice, bpools):
    idxGs = list(enumerate(zip(Gs, slice)))
    idxbpools = list(enumerate(bpools))
    groups = []
    curr_group = []
    for idx, (b, _) in idxbpools:
        # curr_group.append((idx, (b, pool)))
        curr_group.append(idx)
        if not b:
            groups.append(curr_group)
            curr_group = []
    # pprint(groups)

    inner_Gs = []
    for group in groups:
        inner_G = commutable_product_by_group(
            [G for G in idxGs if G[0] in group])
        inner_Gs.append(inner_G)

    # take a product of inner_Gs and chain the results
    for x in itertools.product(*inner_Gs):
        yield itertools.chain(*x)

def enumerate_grammars_aux(grammars, ntss, tss, grammar_ids, hole_infos):
    start_nts = [g[0][0] for g in grammars]
    # zs = zip(grammars, ntss, tss, start_nts, grammar_ids)
    size = len(grammars)
    max_cnt = math.prod(lang_size_grammar(g) for g in grammars)
    cnt = 0

    # 

    # size = 15

    # pool_zs = list(zip(
    #         grammars, ntss, tss, start_nts, grammar_ids, hole_infos))
    # bpools = mk_smarter_slicing_pools(size, pool_zs)
    # test = list(smarter_lattice_slices(bpools, size))
    # pprint(test)
    # assert False

    # 


    while True:
        pool_zs = list(zip(
            grammars, ntss, tss, start_nts, grammar_ids, hole_infos))
        bpools = mk_smarter_slicing_pools(size, pool_zs)
        if bpools is None:
            size += 1 #WARNING WARNING WARNING WARNING WARNING WARNING
            continue
        # print("size", size, flush=True)
        for slice in smarter_lattice_slices(bpools, size):
            # print("SLICE", slice, flush=True)
            if any(x == 0 for x in slice):
                continue
            zs = list(zip(grammars, ntss, tss, start_nts, slice, grammar_ids))
            Gs = [
                enumerate_grammar_memo(*z, debugging=None) 
                for z in zs]
            # prod_Gs = commutable_product_by_groups(Gs, slice, bpools)
            prod_Gs = itertools.product(*Gs)
            for exprs in prod_Gs:
                cnt += 1
                yield exprs
                if cnt >= max_cnt:
                    return
        size += 1 #WARNING WARNING WARNING WARNING WARNING WARNING

# TODO: this function should probably not depend on something so synthesis
# specific as hole_infos. The bs component of mk_smarter_slicing_pools should
# probably be computed in CandidateSpace.
def enumerate_grammars(grammars, experiment_ids, hole_infos):
    # print("Init enumerate grammars OPTIMIZED", flush=True)
    assert(len(grammars) == len(experiment_ids))
    zs = [preprocess_grammar(g, e) for g, e in zip(grammars, experiment_ids)]
    grammars, ntss, tss, grammar_ids = zip(*zs)
    G = enumerate_grammars_aux(grammars, ntss, tss, grammar_ids, hole_infos)
    return G

def enumerate_grammars_unopt(grammars, experiment_ids, hole_infos):
    # print("Init enumerate grammars UNOPTIMIZED", flush=True)
    assert(len(grammars) == len(experiment_ids))
    zs = [preprocess_grammar(g, e) for g, e in zip(grammars, experiment_ids)]
    grammars, ntss, tss, grammar_ids = zip(*zs)
    G = enumerate_grammars_aux_unopt(grammars, ntss, tss, grammar_ids)
    return G

def enumerate_grammar_aux(grammar, nts, ts, grammar_id):
    start_nt = grammar[0][0]
    print("Enumerating start_nt:", start_nt)
    size = 1
    cnt = 0
    max_cnt = lang_size_grammar(grammar)
    # print("MAX_CNT", max_cnt)
    while True:
        # print("cnt", cnt, "size", size, "max_cnt", max_cnt)
        # if size > 10:
        #     pprint(grammar)
        #     assert(False)
        G = enumerate_grammar_memo(grammar, nts, ts, start_nt, size, grammar_id)
        for expr in G:
            cnt += 1
            yield expr
        if cnt >= max_cnt:
            break
        size += 1

# This is just too slow.
def enumerate_grammar_aux_slow(grammar, nts, ts):
    # print("enumerate aux start GRAMMAR", grammar[0])
    queue = list(grammar[0][-1])
    visited = set()
    cnt = 0
    while queue:
        cnt += 1
        # print(cnt, len(queue))
        candidate = queue.pop(0)
        candidate = nested_list_to_nested_tuple(candidate)
        if candidate in visited:
            continue
        visited.add(candidate)
        if nt_free(candidate, nts, ts):
            yield candidate
        # print("EXTENDING...")
        extension = mk_extension(candidate, grammar, nts, ts)
        # print("EXTENSION")
        queue.extend(extension)


def preprocess_grammar(grammar, experiment_id):
    start_nt = grammar[0][0]
    # print("enumerate start GRAMMAR", grammar[0])
    grammar = normalize_grammar(grammar, start_nt)
    nts = set(nt for nt, _, _ in grammar)
    ts = grammar_terminals(grammar, nts)
    grammar_id = hash(nested_list_to_nested_tuple(grammar))
    grammar_id = hash((experiment_id, grammar_id))
    return grammar, nts, ts, grammar_id

def enumerate_grammar(grammar, experiment_id):
    grammar, nts, ts, grammar_id = preprocess_grammar(grammar, experiment_id)
    G = enumerate_grammar_aux(grammar, nts, ts, grammar_id)
    # return (untuple(x, ts) for x in G)
    return G


def _cyclic_deps_aux(deps, nt):
    '''Checks if nt is reachable from itself.
    '''
    # Traverse deps using BFS
    visited = [nt]
    queue = list(deps[nt])
    while queue:
        candidate = queue.pop(0)
        if candidate == nt:
            return True, visited + [nt]
        if candidate in visited:
            continue
        visited.append(candidate)
        if candidate not in deps:
            raise ValueError(f"Expected {candidate} in deps")
        queue.extend(deps[candidate])
    return False, None


def check_for_cyclic_deps(deps):
    '''deps maps non-terminals to sets of non-terminals. This function
    returns True if there is a cycle in the dependencies, and False
    otherwise.
    '''
    for nt in deps.keys():
        b, path = _cyclic_deps_aux(deps, nt)
        if b:
            return True, path
    return False, None

def grammar_is_infinite_aux(grammar, nts, ts):
    '''This function returns True if the grammar is infinite, and False
    otherwise.
    '''
    dependencies = dict()
    visited = set()
    queue = [grammar[0][0]]
    while queue:
        # print("QUEUE", queue)
        candidate = queue.pop(0)
        if candidate in visited:
            continue
        visited.add(candidate)
        rules = list(depth1_nt(grammar, candidate))
        if candidate not in dependencies:
            dependencies[candidate] = set()
        for rule in rules:
            if isinstance(rule, list):
                tail = rule[1:]
                for arg in tail:
                    dependencies[candidate].add(arg)
                    if arg not in visited:
                        queue.append(arg)

    # print("DEPS")
    # pprint(dependencies)
    b, cyclic_nt = check_for_cyclic_deps(dependencies)
    return b, dependencies, cyclic_nt

class EmptyStartNonTerminalError(Exception):
    pass

def grammar_is_infinite_verbose(grammar):
    try:
        grammar = remove_unproductive_non_terminals(grammar)
    except EmptyStartNonTerminalError:
        return False, None, None
    start_nt = grammar[0][0]
    grammar = normalize_grammar(grammar, start_nt)
    nts = set(nt for nt, _, _ in grammar)
    ts = grammar_terminals(grammar, nts)
    return grammar_is_infinite_aux(grammar, nts, ts)

def grammar_is_infinite(grammar):
    b, _, _ = grammar_is_infinite_verbose(grammar)
    return b

def initialize_productive(grammar, ts):
    new_grammar = []
    productive = set()
    for nt, ty, rules in grammar:
        for rule in rules:
            if isinstance(rule, list):
                continue
            elif rule in ts:
                # print("NT", nt, rules)
                productive.add(nt)
                new_grammar.append([nt, ty, rules])
                break
    return new_grammar, productive


def remove_unproductive_non_terminals_aux(grammar, ts, start_nt):
    '''A non-terminal is unproductive if it produces nothing.
    '''
    # print("pre init GRAMMAR", grammar)
    new_grammar, productive = initialize_productive(grammar, ts)
    # print("post init GRAMMAR")
    # pprint(new_grammar)
    # print("remove nt aux PRODUCTIVE", productive)
    fixed_point = False
    while not fixed_point:
        fixed_point = True
        for nt, ty, rules in grammar:
            if nt in productive:
                continue
            for rule in rules:
                if not isinstance(rule, list):
                    continue
                if all(arg in productive for arg in rule[1:]):
                    # print("NT", nt)
                    productive.add(nt)
                    new_grammar.append([nt, ty, rules])
                    fixed_point = False
                    break
    # print("post fixed_point GRAMMAR")
    # pprint(new_grammar)
    if start_nt not in productive:
        raise EmptyStartNonTerminalError(f"Expected {start_nt} in productive")
    new_grammar = rotate_start_nt(new_grammar, start_nt)
    # print("post rotate GRAMMAR")
    # pprint(new_grammar)
    new_start_nt = new_grammar[0][0]
    assert new_start_nt == start_nt, f"Expected {start_nt}, got {new_start_nt}"
    return new_grammar, productive

def remove_unproductive_dependee_rules(grammar, start_nt, productive):
    new_grammar = []
    if start_nt not in productive:
        return new_grammar
    for nt, ty, rules in grammar:
        new_rules = []
        for rule in rules:
            if not isinstance(rule, list):
                new_rules.append(rule)
                continue
            if all(arg in productive for arg in rule[1:]):
                new_rules.append(rule)
        new_grammar.append([nt, ty, new_rules])
    return new_grammar

def remove_unproductive_non_terminals(grammar):
    # print("remove nt GRAMMAR pre norm", grammar)
    start_nt = grammar[0][0]
    grammar = normalize_grammar(grammar, start_nt)
    # print("remove nt GRAMMAR post norm", grammar)
    nts = set(nt for nt, _, _ in grammar)
    ts = grammar_terminals(grammar, nts)
    # print("remove_nt pre aux GRAMMAR", grammar)
    new_grammar, prod = remove_unproductive_non_terminals_aux(
        grammar, ts, start_nt)
    # print("remove_nt post aux GRAMMAR")
    # pprint(new_grammar)
    # print("PRODUCTIVE", prod)
    # Need to remove rules that mention unproductive non-terminals
    # print("remove_nt pre dependee GRAMMAR", new_grammar)
    new_grammar = remove_unproductive_dependee_rules(
        new_grammar, start_nt, prod)
    # print("remove_nt pre dependee GRAMMAR", new_grammar)
    return new_grammar

def lang_size_grammar_s_aux(grammar, nts, ts, start_nt, s, memo_hash, memo={}):
    k = (memo_hash, start_nt, s)
    if k in memo:
        return memo[k]
    # print("lang_size_grammar_s_aux, s=", s)
    if start_nt not in nts:
        raise ValueError(f"Expected {start_nt} in nts")
    res = 0
    grammar = rotate_start_nt(grammar, start_nt)
    for rule in depth1_nt(grammar, start_nt):
        if not isinstance(rule, list) and rule in ts:
            if s == 1:
                res += 1
            continue
        elif s == 1:
            continue
        elif s < 1:
            raise ValueError(f"Expected s >= 1, got {s}")
        # print()
        # print("GRAMMAR")
        # pprint(grammar)
        # print("RULE", rule, ts, [])
        head = rule[0]
        tail = rule[1:]
        for sl in lattice_slices(len(tail), s-1):
            if any(x == 0 for x in sl):
                continue
            tail_sizes = [
                lang_size_grammar_s_aux(
                    grammar, nts, ts, arg, sl[i], memo_hash) 
                for i, arg in enumerate(tail)]
            num_tails = math_prod(tail_sizes)
            res += num_tails
    memo[k] = res
    return res      

def lang_size_grammar_s(grammar, s, memo_hash):
    '''Count the number of expressions of size s generated by the grammar
    '''
    grammar = remove_unproductive_non_terminals(grammar)
    start_nt = grammar[0][0]
    grammar = normalize_grammar(grammar, start_nt)
    nts = set(nt for nt, _, _ in grammar)
    ts = grammar_terminals(grammar, nts)
    return lang_size_grammar_s_aux(
        grammar, nts, ts, start_nt, s, memo_hash)


def lang_size_grammar_aux(grammar, nts, ts, start_nt):
    '''Returns the size of the language generated by the grammar,
    using start_nt as the start non-terminal. Assumes that the grammar
    is not infinite and that all unproductive non-terminals have been
    removed (to avoid infinte, unproductive cycles).
    '''
    if start_nt not in nts:
        raise ValueError(f"Expected {start_nt} in nts")
    res = 0
    grammar = rotate_start_nt(grammar, start_nt)
    for rule in depth1_nt(grammar, start_nt):
        if not isinstance(rule, list) and rule in ts:
            res += 1
            continue
        # print()
        # print("GRAMMAR")
        # pprint(grammar)
        # print("RULE", rule, ts, [])
        head = rule[0]
        tail = rule[1:]
        tail_sizes = [
            lang_size_grammar_aux(grammar, nts, ts, arg) for arg in tail]
        num_tails = math_prod(tail_sizes)
        res += num_tails
    return res        

def lang_size_grammar(grammar):
    '''Returns the size of the language generated by the grammar.
    '''
    grammar = remove_unproductive_non_terminals(grammar)
    start_nt = grammar[0][0]
    grammar = normalize_grammar(grammar, start_nt)
    nts = set(nt for nt, _, _ in grammar)
    ts = grammar_terminals(grammar, nts)
    # pprint(grammar)
    # print(ts)
    if grammar_is_infinite(grammar):
        return float("inf")
    return lang_size_grammar_aux(grammar, nts, ts, start_nt)

def test_grammar_is_infinite(grammar, expected):
    result = grammar_is_infinite(grammar)
    assert result == expected, f"Expected {expected}, got {result}"

def test_remove_unproductive_nt(grammar, expected):
    result = remove_unproductive_non_terminals(grammar)
    assert result == expected, f"Expected {expected}, got {result}"

def test():
    g_simple = [
        ["E", "", [
            "0",
            "1",
            ["+", "E", "E"]]]]
    test_remove_unproductive_nt(g_simple, g_simple)
    test_grammar_is_infinite(g_simple, True)

    # normalization does not change the grammar, so enumeration would
    # continue forever without the removal of unproductive non-terminals
    g_cyclic_empty2 = [
        ["Z", "", ["a", "E"]],
        ["E", "", [["+", "E", "S"]]],
        ["S", "", [["+", "E", "S"]]]]
    test_remove_unproductive_nt(g_cyclic_empty2, [["Z", "", ["a"]]])
    test_grammar_is_infinite(g_cyclic_empty2, False)

    g_simpl_empty = [
        ["S", "", ["a", "E"]],
        ["E", "", ["E"]]]
    test_remove_unproductive_nt(g_simpl_empty, [["S", "", ["a"]]])
    test_grammar_is_infinite(g_simpl_empty, False)

    # normalization produces [], so enumeration would terminate
    g_cyclic_empty1 = [
        ["Z", "", ["a", "E"]],
        ["E", "", ["S"]],
        ["S", "", ["E"]]]
    test_remove_unproductive_nt(g_cyclic_empty1, [["Z", "", ["a"]]])
    test_grammar_is_infinite(g_cyclic_empty1, False)

    # normalization does not change the grammar, so enumeration would
    # continue forever without the removal of unproductive non-terminals
    g_cyclic_empty2 = [
        ["Z", "", ["a", "E"]],
        ["E", "", [["+", "E", "S"]]],
        ["S", "", [["+", "E", "S"]]]]
    test_remove_unproductive_nt(g_cyclic_empty2, [["Z", "", ["a"]]])
    test_grammar_is_infinite(g_cyclic_empty2, False)

    # normalization does not change the grammar, so enumeration would
    # continue forever without the removal of unproductive non-terminals
    g_cyclic_empty3 = [
        ["Z", "", ["a", "E"]],
        ["E", "", [["+", "S", "E"]]],
        ["S", "", ["a"]]]
    test_remove_unproductive_nt(
        g_cyclic_empty3, [["Z", "", ["a"]], ["S", "", ["a"]]])
    test_grammar_is_infinite(g_cyclic_empty3, False)

    # normalization does not change the grammar, since E is productive
    g_cyclic_non_empty1 = [
        ["E", "", [["+", "S", "S"], ["+", "S", "E"]]],
        ["S", "", ["a"]]]
    test_remove_unproductive_nt(g_cyclic_non_empty1, g_cyclic_non_empty1)
    test_grammar_is_infinite(g_cyclic_non_empty1, True)

    # Testing what happens if the start non-terminal is unproductive, but
    # another nt is productive.
    g_start_nt_unproductive = [
        ["E", "", [["+", "E", "E"]]],
        ["S", "", ["a"]]]
    # test_remove_unproductive_nt(g_start_nt_unproductive, []) 
    # ^^^ Expected E in productive
    test_grammar_is_infinite(g_start_nt_unproductive, False)

    # Testing what happens if a productive non-terminal depends on an
    # unproductive non-terminal.
    g_dependee_unproductive = [
        ["E", "", ["a", ["-", "S"]]],
        ["S", "", ["S"]]]
    test_remove_unproductive_nt(g_dependee_unproductive, [["E", "", ["a"]]])
    test_grammar_is_infinite(g_dependee_unproductive, False)
    
    g_trivially_unproductive = [
        ["E", "", ["a"]],
        ["S", "", []]]
    test_remove_unproductive_nt(g_trivially_unproductive, [["E", "", ["a"]]])
    test_grammar_is_infinite(g_trivially_unproductive, False)

if __name__ == "__main__":
    g = {
  "__Reconfig(i, newConfig, newVersion)_g0__": [
    [
      "Start",
      [
        "Start1",
        [
          "not",
          "Start1"
        ]
      ]
    ],
    [
      "Start1",
      [
        "(Rel =)",
        "(Rel set.member)",
        "Bool"
      ]
    ],
    [
      "(Rel set.member)",
      [
        [
          "set.member",
          "(Dom Server)",
          "(Set (Dom Server))"
        ]
      ]
    ],
    [
      "(Rel =)",
      [
        [
          "=",
          "(Dom Server)",
          "(Dom Server)"
        ],
        [
          "=",
          "(Array (Dom Server) (Dom Mode))",
          "(Array (Dom Server) (Dom Mode))"
        ],
        [
          "=",
          "(Dom Mode)",
          "(Dom Mode)"
        ],
        [
          "=",
          "Int",
          "Int"
        ],
        [
          "=",
          "(Array (Dom Server) Int)",
          "(Array (Dom Server) Int)"
        ],
        [
          "=",
          "(Set (Dom Server))",
          "(Set (Dom Server))"
        ],
        [
          "=",
          "(Array (Dom Server) (Set (Dom Server)))",
          "(Array (Dom Server) (Set (Dom Server)))"
        ]
      ]
    ],
    [
      "(Dom Mode)",
      [
        "(Sub (Dom Mode))",
        [
          "select",
          "(Array (Dom Server) (Dom Mode))",
          "(Dom Server)"
        ]
      ]
    ],
    [
      "Int",
      [
        "(Sub Int)",
        [
          "select",
          "(Array (Dom Server) Int)",
          "(Dom Server)"
        ],
        [
          "select",
          "(Array (Dom Server) Int)",
          "(Dom Server)"
        ],
        [
          "+",
          "Int",
          [
            "Int",
            1
          ]
        ]
      ]
    ],
    [
      "(Set (Dom Server))",
      [
        "(Sub (Set (Dom Server)))",
        [
          "select",
          "(Array (Dom Server) (Set (Dom Server)))",
          "(Dom Server)"
        ]
      ]
    ],
    [
      "(Dom Server)",
      [
        "i"
      ]
    ],
    [
      "(Array (Dom Server) (Dom Mode))",
      [
        "state"
      ]
    ],
    [
      "(Sub (Dom Mode))",
      [
        "Primary",
        "Secondary"
      ]
    ],
    [
      "(Sub Int)",
      [
        "newVersion"
      ]
    ],
    [
      "(Array (Dom Server) Int)",
      [
        "currentTerm",
        "configVersion",
        "configTerm"
      ]
    ],
    [
      "(Sub (Set (Dom Server)))",
      [
        "newConfig"
      ]
    ],
    [
      "(Array (Dom Server) (Set (Dom Server)))",
      [
        "config"
      ]
    ],
    [
      "Bool",
      []
    ]
  ]
}
    print(sum(size_fn(v) for k,v in g.items()))