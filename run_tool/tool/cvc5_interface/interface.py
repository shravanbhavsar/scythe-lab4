from pprint import pprint
from cvc5 import Solver, Kind # type: ignore
from sexpdata import loads, dumps
# import utils

# TODO: move me
def recursive_map(seq, func):
    '''Recursively applies func to all elements of seq.'''
    if isinstance(seq, list):
        return [recursive_map(x, func) for x in seq]
    else:
        return func(seq)

# TODO: move me 
def nested_tuple(seq):
    '''Converts a nested list to a nested tuple.'''
    if isinstance(seq, list):
        return tuple([nested_tuple(x) for x in seq])
    else:
        return seq

# https://cvc5.github.io/docs/cvc5-1.0.8/api/python/base/kind.html
RESERVED = {
    '+': Kind.ADD,
    '-': Kind.SUB,
    '*': Kind.MULT,
    'ite': Kind.ITE,
    'and': Kind.AND,
    'or': Kind.OR,
    'not': Kind.NOT,
    '=': Kind.EQUAL,
    '!=': Kind.DISTINCT,
    '<': Kind.LT,
    '<=': Kind.LEQ,
    '>': Kind.GT,
    '>=': Kind.GEQ,
    '=>': Kind.IMPLIES,
    'set.union': Kind.SET_UNION,
    'set.complement': Kind.SET_COMPLEMENT,
    'set.intersection': Kind.SET_INTER,
    'set.singleton': Kind.SET_SINGLETON,
    'set.member' : Kind.SET_MEMBER,
    'set.subset' : Kind.SET_SUBSET,
    'set.filter' : Kind.SET_FILTER,
    'set.card' : Kind.SET_CARD,
    'set.minus' : Kind.SET_MINUS,
    'lambda' : Kind.LAMBDA,
    'variable_list' : Kind.VARIABLE_LIST,
    'tuple' : None,
    'select' : Kind.SELECT,
    'store' : Kind.STORE,
    'exists' : Kind.EXISTS,
    'forall' : Kind.FORALL,
    'arbitraryarray' : None,
    'emptyset' : None,
    'universe' : None,
    'true' : None,
    'false' : None,
}

class Grammar:
    '''A class for capturing grammars in SyGuS.'''
    def __init__(self, sexpr):
        if sexpr is None:
            self.rules = None
            self.init_nt = None
        else:
            self.rules = dict()
            self.init_nt = None
            self.parse_sexpr(sexpr)

    def is_empty(self):
        '''Returns True if the grammar is empty.'''
        return self.rules is None

    def parse_sexpr(self, sexpr):
        '''Parses a sexpr to populate the grammar.'''
        if self.is_empty():
            raise ValueError(
                "Grammar is empty. Call and check is_empty() before calling"
                " parse_sexpr().")
        assert(self.rules is not None)
        for production in sexpr:
            if len(production) != 3:
                raise ValueError("Invalid production: " + str(production))
            nonterminal, srt, rules = production
            if self.init_nt is None:
                self.init_nt = (nonterminal, srt)
            if (nonterminal, srt) in self.rules:
                raise ValueError("Duplicate production: " + str(production))
            self.rules[(nonterminal, srt)] = rules

    def nonterminals(self):
        '''Returns the nonterminals of the grammar.'''
        if self.is_empty():
            raise ValueError(
                "Grammar is empty. Call and check is_empty() before calling"
                " nonterminals().")
        assert(self.rules is not None)
        # return list(self.rules.keys())
        return ([self.init_nt] 
                + [nt for nt in self.rules.keys() if nt != self.init_nt])

class Functar:
    '''A class for capturing a function's type/grammar in SyGuS.'''
    def __init__(self, name, args : list[list], ret, grammar):
        self.name = name
        self.args = [tuple(arg) for arg in args]
        self.ret = ret
        self.grammar = grammar

    def has_empty_grammar(self):
        '''Returns True if the functar has an empty grammar.'''
        return self.grammar.is_empty()
    
    def nonterminals(self):
        '''Returns the nonterminals of the functar's grammar.'''
        if self.has_empty_grammar():
            raise ValueError(
                "Functar has empty grammar. Call and check has_empty_grammar()"
                " before calling nonterminals().")
        return self.grammar.nonterminals()
    
    def get_symbols(self):
        '''Returns arg symbols and nonterminal symbols of the functar's 
        grammar'''
        nts = []
        if not self.has_empty_grammar():
            nts = self.nonterminals()
        return nts + self.args

class cvc5Object:
    '''A class for capturing an abstract cvc5 sygus instance'''
    def __init__(self, logic="LIA"):
        self.var_map = {}
        self.var_sort_map = {}
        self.functar_names = []
        self.sort_map = {}
        self.metasort_map = {}
        self.synthFuns = {}
        self.constants = []

        self._new_const_array = 0

        self.solver = Solver()
        self.solver.setOption("sygus", "true")
        self.solver.setOption("incremental", "true")
        # self.solver.setOption("sygus-enum", "fast")
        self.solver.setLogic(logic)

        if "LIA" in logic:
            self.add_sort("Int")
            self.add_sort("Bool")
        if "FS" in logic:
            self.solver.setOption("sets-ext", "true")
            # self.sort_map["IntSet"] = self.solver.mkSetSort(
            #     self.sort_map["Int"])
            # # TODO: Change the way we handle sets of sets, etc.
            # self.sort_map["IntSetSet"] = self.solver.mkSetSort(
            #     self.sort_map["IntSet"])
            
            # # This is definitely not okay.
            # self.sort_map["IntArrayIntSet"] = self.solver.mkArraySort(
            #     self.sort_map["Int"], self.sort_map["IntSet"])
    
    def get_var_sort(self, var):
        '''Returns the sort of a variable.'''
        return self.var_sort_map[var]

    def add_sort(self, sort):
        '''Adds a sort to the cvc5Object.'''
        if sort in self.sort_map:
            return
        
        if isinstance(sort, str):
            if sort == "Int":
                self.sort_map[sort] = self.solver.getIntegerSort()
            elif sort == "Bool":
                self.sort_map[sort] = self.solver.getBooleanSort()
            else:
                raise NotImplementedError("Sort not implemented: " + sort)
        elif isinstance(sort, tuple):
            if sort[0] == "Array":
                self.add_sort(sort[1])
                self.add_sort(sort[2])
                self.sort_map[sort] = self.solver.mkArraySort(
                    self.sort_map[sort[1]], self.sort_map[sort[2]])
            elif sort[0] == "Set":
                self.add_sort(sort[1])
                self.sort_map[sort] = self.solver.mkSetSort(
                    self.sort_map[sort[1]])
            elif sort[0] == "Tuple":
                tail = sort[1:]
                for s in tail:
                    self.add_sort(s)
                self.sort_map[sort] = self.solver.mkTupleSort(
                    *[self.sort_map[s] for s in tail])
            else:
                raise NotImplementedError("Sort not implemented: " + str(sort))
        else:
            raise ValueError(
                "Expected string or tuple for sort, got: " + str(sort))

    def _handle_constant(self, sexpr):
        '''Converts a constant sexpr to a cvc5 term.'''
        if not isinstance(sexpr, tuple):
            raise ValueError("Invalid constant sexpr: " + str(sexpr))
        if len(sexpr) != 2:
            raise ValueError("Invalid constant sexpr: " + str(sexpr))
        srt = sexpr[0]
        val = sexpr[1]
        if srt == "Int":
            if not isinstance(val, int):
                raise ValueError(
                    "Invalid constant sexpr: " 
                    + str(sexpr) + " expected integer.")
            return self.solver.mkInteger(val)
        elif srt == "Bool":
            if not isinstance(val, bool):
                raise ValueError(
                    "Invalid constant sexpr: " 
                    + str(sexpr) + " expected boolean.")
            return self.solver.mkBoolean(val)
        elif isinstance(srt, tuple) and srt[0] == "Set":
            if val != "emptyset":
                raise ValueError(
                    f"Emptyset only constant supported for sort {srt}.")
            return self.solver.mkEmptySet(self.sort_map[srt])
        else:
            # print(sexpr)
            raise NotImplementedError(
                f"Constants not implemented for sort: {srt}")

    def new_const_array(self, srt):
        const_name = f"__const_array_{self._new_const_array}__"
        self._new_const_array += 1
        v = (const_name, srt)
        self.add_constants([v])
        return self.var_map[v]

    def _sexpr_to_term(self, sexpr):
        '''Converts an sexpr to a cvc5 term.'''
        # pprint(sexpr)
        # print()
        if isinstance(sexpr, list):
            if len(sexpr) == 0:
                raise ValueError(
                    "Empty list in sexpr."
                    " Expected application of reserved symbol or uninterpreted"
                    " function.")
            head = sexpr[0]
            tail = sexpr[1:]
            if isinstance(head, list):
                raise ValueError(
                    "Invalid sexpr: " + str(sexpr) 
                    + " head is a list.")
            if head in ["and", "or"] and len(tail) == 1:
                return self._sexpr_to_term(tail[0])
            elif head == "arbitraryarray":
                if len(tail) != 1:
                    raise ValueError(
                        "Empty array sexpr should have one arg specifying"
                        f"its sort. Got {sexpr}.")
                return self.new_const_array(tail[0])
            elif head == "emptyset":
                raise ValueError(
                    f"Emptysets should now be represented as constants."
                    f" I.e., ({tail[0]}, emptyset). Note tuple not list.")
            elif head == "universe":
                if len(tail) != 1:
                    raise ValueError(
                        "Universe set sexpr should have one arg specifying"
                        f"sort. Got {sexpr}.")
                sort = tail[0]
                try:
                    res = self.solver.mkUniverseSet(self.sort_map[sort])
                except TypeError as e:
                    raise ValueError(
                        f"Invalid sort for universe set: {sort}."
                        " Expected a (nested) tuple.")
                return res
            elif head == "variable_list":
                for v in tail:
                    self._add_var(v, "Var")
                vs = [self.var_map[v] for v in tail]
                return self.solver.mkTerm(Kind.VARIABLE_LIST, *vs)
            elif head == "tuple":
                aux = [self._sexpr_to_term(t) for t in tail]
                return self.solver.mkTuple(aux)
            elif head in RESERVED:
                aux = [self._sexpr_to_term(t) for t in tail]
                try:
                    res = self.solver.mkTerm(RESERVED[head], *aux)
                except RuntimeError as e:
                    print(e)
                    print(sexpr)
                    print(head)
                    print(aux)
                    raise e
                return res
            elif head in self.functar_names:
                aux = [self._sexpr_to_term(t) for t in tail]
                try:
                    return self.solver.mkTerm(
                        Kind.APPLY_UF, self.synthFuns[head], *aux)
                except RuntimeError as e:
                    print(sexpr)
                    print(aux)
                    raise e
            else:
                raise ValueError(f"Unimplemented operation: {sexpr}")
        elif isinstance(sexpr, str):
            if sexpr in self.var_map:
                return self.var_map[sexpr]
            elif sexpr in self.var_sort_map:
                z = (sexpr, self.var_sort_map[sexpr])
                if z not in self.var_map:
                    # print([(x, type(x)) for x,y in self.var_map])
                    print(self.var_map)
                    print(self.var_sort_map)
                    print("sexpr", sexpr, type(sexpr))
                    print("z", z, type(z))
                    raise ValueError("Unknown variable: " + sexpr)
                return self.var_map[z]
            else:
                print(self.var_map)
                print(self.var_sort_map)
                print(sexpr, type(sexpr))
                raise ValueError("Unknown variable: " + sexpr)
        elif isinstance(sexpr, tuple):
            return self._handle_constant(sexpr)
        else:
            raise ValueError("Invalid sexpr: " + str(sexpr))

    def _add_vars(self, vars, metasort : str):
        '''Adds a list of variables to the cvc5Object.'''
        for v in vars:
            self._add_var(v, metasort)

    def _add_var(self, v, metasort : str):
        '''Adds a variable to the cvc5Object. No change is made if the
        variable was already added. We ensure that a variable is not
        declared as both a SygusVar and a Var.
        This helps handle the distinction between 
        - variables used as function parameters (metasort="Var")
        - variables used as non-terminals (metasort="Var")
        - variables used in constraints (metasort="SygusVar")
        - variables representing constants (metasort="Const")
        '''
        if not isinstance(v, tuple) and not isinstance(v, list) or len(v) != 2:
            raise ValueError(
                f"Invalid variable: {v}. Expected tuple or list of length 2."
                "Expected format: (name, sort).")
        v = tuple(v)
        if v[0] in RESERVED:
            raise ValueError(f"Variable name is reserved: {v[0]}.")
        if v not in self.var_map:
            self.var_sort_map[v[0]] = v[1]
            if v[1] not in self.sort_map:
                self.add_sort(v[1])
            self.metasort_map[v[0]] = metasort

            if metasort == "SygusVar":
                self.var_map[v] = self.solver.declareSygusVar(
                    v[0], self.sort_map[v[1]])
            elif metasort == "Var":
                self.var_map[v] = self.solver.mkVar(self.sort_map[v[1]], v[0])
            elif metasort == "Const":
                self.var_map[v] = self.solver.mkConst(self.sort_map[v[1]], v[0])
            else:
                raise ValueError("Invalid metasort: " + metasort)
        if self.metasort_map[v[0]] != metasort:
            raise ValueError(
                f"Variable {v[0]} already declared with a different metasort: "
                f"{v}. Do not reuse variable names across constraints/"
                "functars.")
        
    def add_constants(self, constants):
        '''Adds a list of constants to the cvc5Object.'''
        for c in constants:
            self._add_var(c, "Const")
        self.constants += constants

    def get_constants(self):
        '''Returns the constants of the cvc5Object.'''
        return self.constants

    def add_functar(self, functar : Functar):
        '''Adds a functar to the cvc5Object.'''
        if functar.name in self.functar_names:
            raise ValueError("Functar already exists in cvc5Object")
        if functar.name in RESERVED:
            raise ValueError(f"Functar name is reserved: {functar.name}")
        self.functar_names.append(functar.name)
        
        # Make the symbols for the function/grammar
        self._add_vars(functar.get_symbols(), "Var")
        # Make the grammar for the function
        if functar.has_empty_grammar():
            g = None
        else:
            bound_vars = [self.var_map[arg] for arg in functar.args]
            nonterminals = [self.var_map[nt] for nt in functar.nonterminals()]
            g = self.solver.mkGrammar(bound_vars, nonterminals)
            rule_terms_dict = dict()
            for nt, rules in functar.grammar.rules.items():
                rule_terms_dict[nt] = [
                    self._sexpr_to_term(rule) for rule in rules]
            for nt, rule_terms in rule_terms_dict.items():
                g.addRules(self.var_map[nt], rule_terms)
        # Declare the function-to-synthesize
        f = self.solver.synthFun(
            functar.name,
            [self.var_map[arg] for arg in functar.args],
            self.sort_map[functar.ret],
            g)
        self.synthFuns[functar.name] = f

    def add_constraint(self, constraint):
        '''Adds a constraint to the cvc5Object.'''
        term = self._sexpr_to_term(constraint)
        # term = self.solver.simplify(term)
        self.solver.addSygusConstraint(term)

    def add_assumption(self, assumption):
        '''Adds an assumption to the cvc5Object.'''
        term = self._sexpr_to_term(assumption)
        self.solver.addSygusAssume(term)

    def _fix_solution_aux(self, sol):
        if isinstance(sol, list) and len(sol) > 0 and sol[0] == "as":
            if len(sol) >= 2 and sol[1] == "set.universe":
                sort = nested_tuple(sol[2])
                return ["universe", sort]
            elif len(sol) >= 2 and sol[1] == "set.empty":
                sort = nested_tuple(sol[2])
                # return ["emptyset", sort]
                return (sort, "emptyset")
            else:
                raise ValueError("Invalid as sexpr: " + str(sol))
        elif (isinstance(sol, list) 
              and len(sol) > 0 
              and sol[0] == "set.emptyset"):
            sort = nested_tuple(sol[1])
            return (sort, "emptyset")
        elif isinstance(sol, list):
            tmp = [self._fix_solution_aux(x) for x in sol]
            if len(tmp) == 0:
                return tmp
            elif isinstance(tmp[0], list):
                # If the first element is a list, we make the assumption that
                # cvc5 is returning a variable list.
                vs = []
                for v in tmp:
                    if not isinstance(v, list) or len(v) != 2:
                        raise ValueError(
                            "Invalid variable list: " + str(tmp))
                    v = (v[0], nested_tuple(v[1]))
                    if v not in self.var_map:
                        raise ValueError(
                            "Unknown variable in variable list: " + str(v))
                    vs.append(v)
                return ["variable_list", *vs]
            else:
                return tmp
        elif sol == "true":
            return ("Bool", True)
        elif sol == "false":
            return ("Bool", False)
        elif sol.isnumeric():
            return ("Int", int(sol))
        elif isinstance(sol, str):
            return sol
        else:
            raise ValueError(f"Invalid sexpr {sol}")

    def _fix_solution(self, sol):
        '''Takes cvc5 solution or and converts it to the central format.'''
        sol = loads(str(sol))
        dumps_clean = lambda x : dumps(x).replace("\\", "") # strip out any backslashes/escaping explicitly.
        sol = recursive_map(sol, dumps_clean)
        interpretation = sol[-1]
        interpretation = self._fix_solution_aux(interpretation)
        return interpretation
        
    def solve(self):
        '''Solves the sygus instance.'''
        # Very important to push/pop since CVC5 maintains some kind of internal
        # state that prevents the same interpretation from being returned twice 
        # for any given unint function.
        # This only a problem when there are multiple functions to synthesize.
        self.solver.push()
        x = self.solver.checkSynth()
        if not x.hasSolution():
            return None

        # terms = [self.synthFuns[uf] for uf in self.functar_names]
        # sols = self.solver.getSynthSolutions(terms)
        # # This assumes that the solver returns the interpretations in the
        # #   same order as the terms were given in the above function call.
        # sols = zip(self.functar_names, sols)
        sols = [(uf, self.solver.getSynthSolutions([self.synthFuns[uf]])[0]) 
                for uf in self.functar_names]
        res = {}
        for functar, sol in sols:
            # print(functar, type(functar))
            interpretation = self._fix_solution(sol)
            # This call should not throw an error after the above call
            self._sexpr_to_term(interpretation)
            res[functar] = interpretation
        self.solver.pop()
        return res