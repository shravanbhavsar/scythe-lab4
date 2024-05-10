from interface import Functar, Grammar
from interface import cvc5Object

min_max_g_sexpr = [
    ['Start', 'Int',
        ['a0',
        'a1',
        ('Int', 0),
        ('Int', 1),
        ['+', 'Start', 'Start'],
        ['-', 'Start', 'Start'],
        ['ite', 'StartBool', 'Start', 'Start']]],
    ['StartBool', 'Bool',
        [
            ['and', 'StartBool', 'StartBool'],
            ['or', 'StartBool', 'StartBool'],
            ['not', 'StartBool'],
            ['<=', 'Start', 'Start'],
            ['=', 'Start', 'Start']]]]
min_max_g = Grammar(min_max_g_sexpr)

# The max2 example
max2 = Functar(
    'max2',
    [['a0', 'Int'], ['a1', 'Int']],
    'Int',
    min_max_g)
two_vars = [['x0', 'Int'], ['x1', 'Int']]
cvcObj = cvc5Object()
cvcObj.add_functar(max2)
cvcObj.add_constraint(two_vars, ['>=', ['max2', 'x0', 'x1'], 'x0'])
cvcObj.add_constraint(two_vars, ['>=', ['max2', 'x0', 'x1'], 'x1'])
cvcObj.add_constraint(
    two_vars, 
    ['or', ['=', ['max2', 'x0', 'x1'], 'x0'], 
           ['=', ['max2', 'x0', 'x1'], 'x1']])
sols = cvcObj.solve()
assert(sols)
sol = sols[0]
print(sol)
