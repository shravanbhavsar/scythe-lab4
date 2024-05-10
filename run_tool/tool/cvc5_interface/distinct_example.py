from pprint import pprint
from interface import cvc5Object, Functar, Grammar

# distinct example
distinct_g_sexpr = [
    ['Start', 'Bool',
        [
            ['and', 'Start', 'Start'],
            ['not', 'Start'],
            ['=', 'Number', 'Number']]],
    ['Number', 'Int',
        ['a0', 'a1', 'a2']],
]
distinct_g = Grammar(distinct_g_sexpr)
distinct = Functar(
    'distinct',
    [['a0', 'Int'], ['a1', 'Int'], ['a2', 'Int']],
    'Bool',
    distinct_g)
two_vars = [['x0', 'Int'], ['x1', 'Int'], ['x2', 'Int']]
cvcObj = cvc5Object()
cvcObj.add_functar(distinct)
cvcObj.add_constraint(
    two_vars, ['=', ['distinct', 'x0', 'x1', 'x2'], ['!=', 'x0', 'x1', 'x2']])
sols = cvcObj.solve()
assert(sols)
sol = sols[0]
pprint(sol)