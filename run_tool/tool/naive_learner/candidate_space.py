from pprint import pprint
from itertools import product
import queue
import traceback
# import threading
import multiprocessing
import time

from .grammar_enum import enumerate_grammar, enumerate_grammars, enumerate_grammars_unopt, grammar_is_infinite, lang_size_grammar, lang_size_grammar_s, nested_list_to_nested_tuple, size_fn
from ..tlc_interface.pprinting import sexp_to_tla
from ..constraint_inference import eval_expression
from .dovetail import dovetail_product as doveproduct, lattice_slices
from .dovetail import interleave

class CandidateSpace:

    def __init__(
            self, sketch, functars, constants, logic, hole_infos,
            assumptions=None, optimize=None):

        self.optimize = optimize
        if optimize is None:
            self.optimize = True

        self.sketch = sketch
        self.functars = functars
        self._constraints = []
        self.generator = self.mk_generator()
        self._constants = constants
        if assumptions is None:
            assumptions = []
        self._assumptions = assumptions
        self._size = None
        self._elim_before_model_checking = 0
        self.iteration = 0
        self.expr_size = 0
        self.cand_num = 0
        self._expr_counts = {}
        self.hole_infos = hole_infos

        self._protocols = set()

        self.queue = multiprocessing.Queue()
        t1 = multiprocessing.Process(
            target=self.producer, daemon=True) # type: ignore
        t1.start()

        self.get_constant_map()

    def get_grammars(self):
        return {f[0] : f[3] for f in self.functars}

    def get_eliminated(self):
        return self._elim_before_model_checking

    def get_depends(self, ufn):
        for f in self.functars:
            if f[0] == ufn:
                return f[1]
        raise ValueError(f"Function {ufn} not found")

    def is_constant(self, val):
        if not isinstance(val, str):
            return False
        return any(val == c[0] for c in self._constants)

    def get_constant_map(self):
        constant_map = {}
        for assume in self._assumptions:
            if assume[0] == "=":
                left = assume[1]
                right = assume[2]
                if self.is_constant(right) and not self.is_constant(left):
                    constant_map[right] = left
                elif self.is_constant(left) and not self.is_constant(right):
                    constant_map[left] = right
        # pprint(self._constants)
        for c in self._constants:
            # print(c)
            if c[0] not in constant_map:
                constant_map[c[0]] = c[0]
        return constant_map

    # TODO: this should take advantage of smart_lattice_slices
    def _compute_expr_count(self, n):
        count = 0

        nfs = len(self.functars)
        for idx, sl in enumerate(lattice_slices(nfs, n)):
            # print(idx, sl)
            inner_count = 1
            if any(s == 0 for s in sl):
                continue
            for s, f in zip(sl, self.functars):
                _, _, _, grammar_raw = f
                if s == 0:
                    continue
                memo_hash = hash(tuple(f2[0] for f2 in self.functars[:idx]))
                memo_hash = hash((memo_hash, f[0]))
                inner_count *= lang_size_grammar_s(grammar_raw, s, memo_hash)

            count += inner_count

        self._expr_counts[n] = count

    def count_exprs(self, n):
        '''Returns the number of expressions in the grammar of size n.
        '''
        if n not in self._expr_counts:
            self._compute_expr_count(n)
        return self._expr_counts[n]


    def get_size(self):
        if self._size is None:
            self._compute_size()
        return self._size

    def _compute_size(self):
        '''Compute the size of the candidate space. This is the product of the
        number of possible interpretations for each functar.
        '''
        sub_counts = []
        for f in self.functars:
            if not isinstance(f, list) and len(f) == 4:
                raise ValueError("Invalid functar: " + str(f))
            _, _, _, grammar_raw = f
            if grammar_is_infinite(grammar_raw):
                self._size = float("inf")
                return
            sub_count = lang_size_grammar(grammar_raw)
            sub_counts.append(sub_count)
        self._size = 1
        for count in sub_counts:
            self._size *= count

    def mk_generator(self):
        grammars = []
        ids = []
        for i, f in enumerate(self.functars):
            print(f'grammar {i + 1}: {f}')
        exp_id = hash(
            tuple([hash(nested_list_to_nested_tuple(f[3]))
            for f in self.functars]))
        hole_infos = [
            {
                "is_guard": self.hole_infos[the_functar[0]]["is_guard"],
                "action":  self.hole_infos[the_functar[0]]["action"],
            }
            for the_functar in self.functars
        ]
        for f in self.functars:
            grammar = f[3]
            grammars.append(grammar)
            hole_id = hash((f[0], exp_id))
            ids.append(hole_id)
        if self.optimize:
            print("OPTIMIZED")
            G = enumerate_grammars(grammars, ids, hole_infos)
        else:
            print("UNOPTIMIZED")
            G = enumerate_grammars_unopt(grammars, ids, hole_infos)
        # print("Querying enumerate grammars")
        for prod_sol in G:
            # print("Got enumerate grammars")
            sygus_solutions = {}
            for i, sol in enumerate(prod_sol):
                sygus_solutions[self.functars[i][0]] = sol
            yield sygus_solutions
            # print("Querying enumerate grammars")

    def _validate_hole(self, hole_name):
        if not hole_name.startswith("__"):
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must start with two underscores.")
        if not hole_name.endswith("__"):
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must end with two underscores.")
        if self.sketch.count(hole_name) != 1:
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must appear exactly once in the sketch."
                f" Found {self.sketch.count(hole_name)} instances.")

    def _instantiate_sketch(self, sygus_solutions):
        if len(self.functars) != len(sygus_solutions.items()):
            raise ValueError(
                "Number of solutions does not match number of functars.")
        tmp = str(self.sketch)
        for hole, instantiation in sygus_solutions.items():
            if hole not in tmp:
                raise ValueError(f"Cannot find hole {hole} in sketch")
            tmp = tmp.replace(hole, sexp_to_tla(instantiation))
        return tmp, sygus_solutions

    def _check_clause(self, clause, sygus_solutions):
        ufn, inputs, output = clause
        new_expression = sygus_solutions[ufn]

        eval = eval_expression(new_expression, inputs)

        return eval != output

    def _check_constraint(self, con, sygus_solutions):
        return any(
            self._check_clause(clause, sygus_solutions) for clause in con)

    def _check_constraints(self, sygus_solutions):
        return all(
            self._check_constraint(
                con, sygus_solutions) for con in self._constraints)

    def pick(self, timeout=None):
        # print("\nentered pick")
        self.cand_num += 1
        sygus_solutions = self.generate(timeout=timeout)
        while (sygus_solutions is not None
               and not self._check_constraints(sygus_solutions)):
            self._elim_before_model_checking += 1
            sygus_solutions = self.generate(timeout=timeout)
        print()
        if sygus_solutions is None:
            return None, None
        return self._instantiate_sketch(sygus_solutions)

    def producer(self):
        error = None
        while True:
            if self.queue.qsize() > 0:
                continue
            try:
                x = next(self.generator)
            except StopIteration:
                x = None
            except Exception as e:
                tb = traceback.format_exc()
                error = e
            finally:
                if error is not None:
                    print(tb)
                    break
            self.queue.put(x)
        self.queue.put(error)

    def is_repeat(self, x):
        if str(x) in self._protocols:
            return True
        self._protocols.add(str(x))

    def generate(self, timeout=None):
        # return self.mock_generate()
        if self._elim_before_model_checking % 70 == 0:
            if self._elim_before_model_checking % 140 == 0:
                close = " |"
            else:
                close = "---"
            print(close, flush=True)
            print(
                f"Picking candidate {self.cand_num}"
                f" (expr_size: {self.expr_size})", end="", flush=True)
        print(".", end="", flush=True)

        x = self.queue.get()
        if isinstance(x, Exception):
            raise x
        # print("_CAND: ", x, flush=True)

        if x is None:
            return None

        # if self.is_repeat(x):
        #     assert False, "Repeated candidate"

        ox = x
        x = [v for _, v in x.items()]
        x_size = sum(size_fn(z) for z in x)
        if x_size < self.expr_size:
            raise RuntimeError(
                "Expression size should be non-decreasing."
                f" x_size: {x_size}, self.expr_size: {self.expr_size}")
        self.expr_size = x_size
        return ox

    def mock_generate(self):
        self.iteration += 1
        if self.iteration == 2:
            return {
                '__Unlock(n)_g0__': ['select', 'holds_lock', 'n'],
                '__Unlock(n)_grant_msg__': 'grant_msg',
                '__Unlock(n)_holds_lock__':
                    ['store', 'holds_lock', 'n', ('Bool', False)],
                '__Unlock(n)_lock_msg__': 'lock_msg',
                '__Unlock(n)_unlock_msg__':
                    ['store', 'unlock_msg', 'n', ('Bool', True)]}
        return {
            '__Unlock(n)_g0__': ['not', ['select', 'grant_msg', 'n']],
            '__Unlock(n)_grant_msg__': 'grant_msg',
            '__Unlock(n)_holds_lock__': 'holds_lock',
            '__Unlock(n)_lock_msg__':
                ['store', 'lock_msg', 'n', ('Bool', False)],
            '__Unlock(n)_unlock_msg__': 'unlock_msg'
        }

    def prune(self, con):
        self._constraints.append(con)


