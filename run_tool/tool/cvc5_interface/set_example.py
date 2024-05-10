from pprint import pprint
from interface import cvc5Object, Grammar, Functar
# https://cvc5.github.io/docs/cvc5-1.0.8/examples/sets.html

g_sexpr = [
    ['Start', 'IntSet',
        [
            'A0', 'A1',
            ['union', 'Start', 'Start'],
            ['complement', 'Start'],
        ]]]
g = Grammar(g_sexpr)
f = Functar(
    'intersect',
    [['A0', 'IntSet'], ['A1', 'IntSet']],
    'IntSet',
    g)



cvcObj = cvc5Object(logic="LIAFS")
cvcObj.add_functar(f)
cvcObj.add_constraint(
    [['x0', 'IntSet'], ['x1', 'IntSet']],
    ['=', ['intersect', 'x0', 'x1'], ['intersection', 'x0', 'x1']])
sols = cvcObj.solve()
assert(sols)
sol = sols[0]
pprint(sol)