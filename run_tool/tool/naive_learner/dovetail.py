'''The itertools.produt does not dovetail its input generators. This module
implemens a dovetailing version of itertools.product.
'''
from itertools import product
from pprint import pprint

class IndexedGenerator:

    def __init__(self, generator):
        self.generator = generator
        self.memo = []

    def __getitem__(self, index):
        while len(self.memo) <= index:
            self.memo.append(next(self.generator, None))
        return self.memo[index]
    
def smarter_lattice_slices_rec(bpools, n, memo={}):
    '''Arguments:
    - bpools: a tuple of doubles. Each double is a boolean-frozen set pair. The
      boolean indicates whether the value of that pool should be less than the
      value of the next pool.
    - n: a non-negative integer.
    - memo: a dictionary that caches the results of previous calls to
      smart_lattice_slices.

    Assumptions: - for all i and x in pools[i], x <= n (guaranteed by mutual
    recursion with
      smart_lattice_slices).

    Yields all (y1, y2, ..., yk) where y1, y2, ..., yk are non-negative integers
    such that y1 + y2 + ... + yk = n and y1 in pools[0][1], y2 in pools[1][1],
    ..., yk in pools[k][1]. Furthermore, for all i, y_i <= y_{i+1} if
    pools[i][0] == True 
    '''
    # if any(any(x > n for x in p) for p in pools):
    #     raise ValueError(f"Must have all x <= n, got {pools, n}")
    if (bpools, n) in memo:
        for s in memo[(bpools, n)]:
            yield s
    elif n < 0 or len(bpools) < 1:
        raise ValueError(
            f"Must be n >= 0 and len(bpools) > 1, got {bpools, n}")
    elif len(bpools) == 1 and n in bpools[0][1]:
        res = (n,)
        memo[(bpools, n)] = [res]
        yield res
    elif len(bpools) == 1: # and n not in bpools[0][1]
        memo[(bpools, n)] = []
    elif n == 0 and all(0 in pool for _, pool in bpools):
        res = (0,) * len(bpools)
        memo[(bpools, n)] = [res]
        yield res
    elif n == 0: # and not all(0 in p for p in pools)
        memo[(bpools, n)] = []
    else:
        # DO_NOT add each res to memo[(pools,n)] as you get it. Cache it in
        # to_flush and then flush to memo[(pools,n)] at the end. Otherwise you
        # may end up with a partial memo entry that breaks things when you make
        # a new call to smarter_lattice_slices.
        to_flush = []
        for i in sorted(bpools[0][1], reverse=True):
            for s in smarter_lattice_slices(bpools[1:], n - i):
                # print(8 - len(bpools), i, n, s[0])
                if bpools[0][0] and (s[0] < i):
                    break
                res = (i,) + s
                to_flush.append(res)
                yield res
        memo[(bpools, n)] = to_flush

def smarter_lattice_slices(bpools, n):
    '''See smarter_lattice_slices_rec. (sorry)
    '''
    new_bpools = tuple((
        b, frozenset([
            x for x in pool if x <= n])) 
        for b, pool in bpools)
    for s in smarter_lattice_slices_rec(new_bpools, n):
        yield s

def smart_lattice_slices_rec(pools, n, memo={}):
    '''Arguments:
    - pools: a tuple of frozensets of non-negative integers.
    - n: a non-negative integer.
    - memo: a dictionary that caches the results of previous calls to
      smart_lattice_slices.

    Assumptions: 
    - for all i and x in pools[i], x <= n (guaranteed by mutual recursion with
      smart_lattice_slices).

    Yields all (y1, y2, ..., yk) where y1, y2, ..., yk are non-negative integers
    such that y1 + y2 + ... + yk = n and y1 in pools[0], y2 in pools[1], ..., yk
    in pools[k].
    '''
    # if any(any(x > n for x in p) for p in pools):
    #     raise ValueError(f"Must have all x <= n, got {pools, n}")
    if (pools, n) in memo:
        for s in memo[(pools, n)]:
            yield s
    elif n < 0 or len(pools) < 1:
        raise ValueError(
            f"Must be n >= 0 and len(pools) > 1, got {pools, n}")
    elif len(pools) == 1 and n in pools[0]:
        res = (n,)
        memo[(pools, n)] = [res]
        yield res
    elif len(pools) == 1: # and n not in pools[0]
        memo[(pools, n)] = []
    elif n == 0 and all(0 in p for p in pools):
        res = (0,) * len(pools)
        memo[(pools, n)] = [res]
        yield res
    elif n == 0: # and not all(0 in p for p in pools)
        memo[(pools, n)] = []
    else:
        # DO_NOT add each res to memo[(pools,n)] as you get it. Cache it in
        # to_flush and then flush to memo[(pools,n)] at the end. Otherwise you
        # may end up with a partial memo entry that breaks things when you make
        # a new call to smart_lattice_slices.
        to_flush = []
        for i in sorted(pools[0]):
            for s in smart_lattice_slices(pools[1:], n - i):
                res = (i,) + s
                to_flush.append(res)
                yield res
        memo[(pools, n)] = to_flush

def smart_lattice_slices(pools, n):
    '''See smart_lattice_slices_rec. (sorry)
    '''
    new_pools = tuple(frozenset([x for x in pool if x <= n]) for pool in pools)
    for s in smart_lattice_slices_rec(new_pools, n):
        yield s

def lattice_slices(x, n, memo={}):
    '''Generates all x-tuples of non-negative integers that sum to n. 
    '''
    # print(x,n)
    if (x, n) in memo:
        # print("cache hit", n)
        for s in memo[(x, n)]:
            yield s
    elif n < 0 or x < 1:
        raise ValueError(f"Must be n >= 0 and x > 0, got {n,x}")
    elif x == 1:
        res = (n,)
        memo[(x, n)] = [res]
        yield res
    elif n == 0:
        res = (0,) * x
        memo[(x, n)] = [res] 
        yield res
    else:
        # DO_NOT add each res to memo[(x,n)] as you get it. Cache it in to_flush
        # and then write to_flush to memo[(x,n)] at the end. Otherwise you may
        # end up with a partial memo entry that breaks things when you make a
        # new call to lattice_slices. 
        to_flush = []
        for i in range(n + 1):
            for s in lattice_slices(x - 1, n - i):
                res = (i,) + s
                to_flush.append(res)
                yield res
        memo[(x, n)] = to_flush
def all_lattice_slices(x):
    '''Generates all x-tuples of non-negative integers.
    '''
    for n in nats():
        for s in lattice_slices(x, n):
            yield s

def commutable_product_aux(gs, N=None):
    '''Will yield all n-tuples of the form ((i1, x1), (i2, x2), ..., (in, xn))
    where i1 <= i2 <= ... <= in and xj is the ijth element of the jth generator.
    E.g. if gs = [[0,1], [0,1]], then the output will be ((0,0), (0,0)), ((1,1),
    (0,0)), ((1,1), (1,1)). Notice that ((0,0), (1,1)) is not in the output
    because 1 < 0. Assumes all gs have the same behavior.
    '''
    if len(gs) == 0:
        raise ValueError("Must have at least one generator")
    if len(gs) == 1:
        idx = 0
        while N is None or idx <= N:
            res = gs[0][idx]
            if res is None:
                break
            yield ((idx, res),)
            idx += 1
    else:
        head = gs[0]
        tail = gs[1:]
        idx = 0
        while N is None or idx <= N:
            res = head[idx]
            if res is None:
                break
            for s in commutable_product_aux(tail, N=idx):
                yield ((idx, res),) + s
            idx += 1

def commutable_product(gs):
    gs = [IndexedGenerator(g) for g in gs]
    for p in commutable_product_aux(gs):
        yield tuple(x[1] for x in p)

def dovetail_product(gs):
    '''Yield the cartesian product of the generators gs, dovetailing the
    generators.
    '''
    gs = [IndexedGenerator(g) for g in gs]
    sizes = [0 for _ in gs]
    for ntuple in all_lattice_slices(len(gs)):
        res = tuple(g[ntuple[i]] for i, g in enumerate(gs))
        for i, r in enumerate(res):
            if r is not None:
                sizes[i] += 1
        if all(x is None for x in res):
            break
        # If any constituent generator is a priori empty then we need to 
        # terminate. Otherwise we will loop forever on (x_i,...,None) where
        # x_i are the elements of some infinite generator
        if any(r is None and sizes[i] == 0 for i, r in enumerate(res)):
            break
        # If we've exhausted the generator, but it is not a priori empty, then
        # we can keep going. Eventually we will look at ntuple that refers to
        # an element of the generator that is not None.
        if any(x is None for x in res):
            continue
        yield res

def interleave(gs):
    spent = [False for _ in gs]
    while True:
        if all(spent):
            break
        for i, g in enumerate(gs):
            res = next(g, None)
            if res is None:
                spent[i] = True
                continue
            yield res

def xrange(n):
    '''Yield the natural numbers less than n.
    '''
    i = 0
    while i < n:
        yield i
        i += 1

def nats():
    '''Yield the natural numbers.'''
    n = 0
    while True:
        yield n
        n += 1

def ab_words_n(n):
    '''Yields all n-length words over the alphabet {a, b}.
    '''
    if n == 0:
        yield ""
    else:
        for w in ab_words_n(n-1):
            yield w + "a"
            yield w + "b"

def ab_words():
    '''Yields all words over the alphabet {a, b}.
    '''
    for n in nats():
        for w in ab_words_n(n):
            yield w

def test_dovetail_product():
    X = [nats(), nats(), nats()]
    for p in dovetail_product(X):
        if sum(p) > 5:
            break
        print(p)
    print()
    X = [xrange(2), nats(), xrange(3)]
    for p in dovetail_product(X):
        if sum(p) > 10:
            break
        print(p)
    # X = [ab_words(), ab_words(), ab_words()]
    # for p in dovetail_product(X):
    #     if all(len(w) > 1 for w in p):
    #         break
    #     print(sum(len(w) for w in p))

if __name__ == "__main__":
    for x in commutable_product([range(3), range(3), range(3)]):
        print(x)