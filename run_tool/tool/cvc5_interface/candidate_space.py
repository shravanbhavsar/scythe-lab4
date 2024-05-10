'''A module encapsulating the universe of TLA+ completions.'''
from pprint import pprint
from cvc5_interface.interface import cvc5Object, Functar, Grammar
from tlc_interface.pprinting import sexp_to_tla
from copy import deepcopy

class CandidateSpace:
    '''A class representing the universe of TLA+ programs.
    The universe is parameterized by a TLA+ sketch and a set of Functars.
    We say that an element is in the universe if it is a completion of the
    sketch conforming to the shape of the Functars.
    
    This class supports two operations:
    1. pick: pick an element from the universe.
    2. prune: prune elements from the universe.
    '''

    def __init__(self, sketch, functars, constants, logic, assumptions=None):
        '''Initialize the universe.
        Args:
            sketch: a TLA+ sketch.
            functars: a list of Functars.
        '''
        if assumptions is None:
            assumptions = []
        self.sketch = sketch
        self.functars = deepcopy(functars)
        self._sygus_object = cvc5Object(logic=logic)
        self._sygus_object.add_constants(constants)
        self._constants = []
        for constant in constants:
            self._constants.append(constant)
        for functar in self.functars:
            if not isinstance(functar, Functar):
                if not isinstance(functar, list) and len(functar) == 4:
                    raise ValueError("Invalid functar: " + str(functar))
                name, args, ret, grammar_raw = functar
                self._validate_hole(name)
                grammar = Grammar(grammar_raw)
                functar = Functar(name, args, ret, grammar)
            self._sygus_object.add_functar(functar)
        for assumption in assumptions:
            self._sygus_object.add_assumption(assumption)

    def is_constant(self, v):
        '''Check if the given value is a constant.'''
        if not isinstance(v, str):
            return False
        return any(v == c[0] for c in self._constants)

    def _validate_hole(self, hole_name):
        '''Check if the given hole name is valid.
        A hole name should start and end with two underscores.
        Also, the hole name should appear exactly once in the sketch.
        Raises ValueError if the hole name is invalid.
        '''
        if not hole_name.startswith("__"):
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must start with two underscores.")
        if not hole_name.endswith("__"):
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must end with two underscores.")
        if self.sketch.count(hole_name) != 1:
            # print(self.sketch)
            raise ValueError(
                f"Invalid hole name: {hole_name}."
                " Must appear exactly once in the sketch."
                f" Found {self.sketch.count(hole_name)} instances.")

    def _instantiate_sketch(self, sygus_solutions):
        '''Instantiate the sketch with the given sygus solutions.'''
        if len(self.functars) != len(sygus_solutions.items()):
            raise ValueError(
                "Number of solutions does not match number of functars.")
        tmp = str(self.sketch)
        for hole, instantiation in sygus_solutions.items():
            if hole not in tmp:
                raise ValueError(f"Cannot find hole {hole} in sketch")
            tmp = tmp.replace(hole, sexp_to_tla(instantiation))
        # return tmp, list(sygus_solutions.items())[0][-1]
        return tmp, sygus_solutions

    def pick(self):
        '''Pick an element from the candidate space.
        Returns:
            - A TLA+ program.
            - Instantiations of the program holes.
            None, None indicates that the constrained 
            candodate space is empy
        '''
        sygus_solutions = self._sygus_object.solve()
        if sygus_solutions is None:
            return None, None
        return self._instantiate_sketch(sygus_solutions)

    def get_depends(self, ufn):
        for f in self.functars:
            if f[0] == ufn:
                return f[1]
        raise ValueError(f"Function {ufn} not found")
    
    def get_ufn_sort(self, ufn):
        for f in self.functars:
            if f[0] == ufn:
                return f[2]
        raise ValueError(f"Function {ufn} not found")
    
    def get_var_sort(self, var):
        return self._sygus_object.get_var_sort(var)

    def prune(self, prune_expr):
        '''Prune elements from the candidate space.
        prune_expr is a list of triples (ufn, inputs, output).
        '''
        constraint : list = ["or"]
        # for ufn, inputs, interpretation, valuation, sorts in prune_expr:
        #     ufn_args = [eval_interp(x, valuation, sorts) for x in inputs]
        #     output = eval_interp(interpretation, valuation, sorts)
        #     ufn_applied = [ufn] + ufn_args
        #     eq = ["=", ufn_applied, output]
        #     neq = ["not", eq]
        #     constraint.append(neq)
        for ufn, inputs, output in prune_expr:
            inputs = {
                k : self.python_to_cvc5(v, self.get_var_sort(k)) 
                for k, v in inputs.items()}
            ufn_args = self.get_depends(ufn)
            ufn_applied = [ufn] + [inputs[x[0]] for x in ufn_args]
            ufn_sort = self.get_ufn_sort(ufn)
            eq = ["=", ufn_applied, self.python_to_cvc5(output, ufn_sort)]
            neq = ["not", eq]
            constraint.append(neq)
        
        self._sygus_object.add_constraint(constraint)

    def python_to_cvc5(self, data, sort):
        if self.is_constant(data):
            return data
        elif isinstance(data, set):
            res = (sort, "emptyset")
            for x in data:
                res = [
                    "set.union", 
                    res, 
                    ["set.singleton", self.python_to_cvc5(x, sort[1])]]
            return res
        elif isinstance(data, bool):
            return ("Bool", data)
        elif isinstance(data, dict):
            res = ["arbitraryarray", sort]
            for k, v in data.items():
                k = self.python_to_cvc5(k, sort[1])
                v = self.python_to_cvc5(v, sort[2])
                res = ["store", res, k, v]
            return res
        elif isinstance(data, tuple):
            return (["tuple"] 
                    + [self.python_to_cvc5(x, sort[i+1]) 
                       for i, x in enumerate(data)])
        else:
            raise ValueError(f"Unsupported data type: {data}")
    

def eval_interp(interp, mapping, sorts):
    '''Given an interpretation interp of an uninterpreted function,
    substitute the values in mapping for the variables in interp.
    '''
    if isinstance(interp, list):
        return [eval_interp(x, mapping, sorts) for x in interp]
    else:
        aux = mapping.get(interp, interp)
        sort = sorts.get(interp, None)
        if sort is not None:
            if not isinstance(aux, str):
                return aux
            return parse_value(sort, aux)
        return aux
    

# The following function is critical for parsing violations, but it is not used
# to convert the tlc output into the TLCViolation data structure. Instead, it is
# used to parse the strings stored in the state / params fields of the 
# TLCViolation / TLCTransition data structures. This function is intended to be
# used by the constraint inference module.
def parse_value(sort, s):
    '''Convert a string s representing the value of TLA+ state variable
    or action argument into an sexpr representing the same value.
    '''
    if not isinstance(s, str):
        raise ValueError(
            f"Expected string, got {s}. Do not pass non-string to parse_value.")
    if sort == "Int":
        try:
            return ("Int", int(s))
        except:
            pass
        return s
    elif sort == "Bool":
        if s == "TRUE":
            return ("Bool", True)
        elif s == "FALSE":
            return ("Bool", False)
        else:
            raise ValueError(f"Unexpected boolean value: {s}")
    elif isinstance(sort, tuple) and sort[0] == "Set":
        if not (s.startswith("{") and s.endswith("}")):
            raise ValueError(
                f"State variable of sort {sort}"
                f"has unexpected value {s}")
        aux = s[1:-1].replace(" ", "")
        if sort[1] == "Int":
            if aux == "":
                # res = ["emptyset", sort]
                res = (sort, "emptyset")
            else:
                aux = aux.split(",")
                # res = ["emptyset", sort]
                res = (sort, "emptyset")
                aux = [parse_value(sort[1], x) for x in aux]
                for x in aux:
                    res = ["set.union", res, ["set.singleton", x]]
            return res
        # TODO: Use an actual parser to handle this sort of nested datatype.
        if sort[1] == ("Tuple", "Int", "Int"):
            if aux == "":
                # res = ["emptyset", sort]
                res = (sort, "emptyset")
            else:
                aux = aux.split(">>,<<")
                aux = [x.replace("<", "").replace(">", "") for x in aux]
                aux = [f"<<{x}>>" for x in aux]
                # res = ["emptyset", sort]
                res = (sort, "emptyset")
                aux = [parse_value(sort[1], x) for x in aux]
                for x in aux:
                    res = ["set.union", res, ["set.singleton", x]]
            return res
        else:
            raise NotImplementedError(
                f"Sets over sort {sort[1]} not yet supported as "
                f"state variables or arguments to actions.")
    elif isinstance(sort, tuple) and sort[0] == "Array":
        kvs = s[1:-1].split("@@")
        kvs = [tuple(x.split(":>")) for x in kvs]
        # The theory of arrays does not support "empty" arrays.
        # For our purposes, storing key-value pairs in an
        # "arbitrary" array is sufficient. We don't care about
        # the contents of the array aside from these key-value pairs.
        res = ["arbitraryarray", sort]
        for k, v in kvs:
            k = parse_value(sort[1], k)
            v = parse_value(sort[2], v)
            res = ["store", res, k, v]
        return res
    elif isinstance(sort, tuple) and sort[0] == "Tuple":
        aux = s[2:-2].split(",")
        aux = [parse_value(x, y) for x,y in zip(sort[1:], aux)]
        return ["tuple"] + aux
    else:
        raise NotImplementedError(f"Sort {sort} not yet supported")