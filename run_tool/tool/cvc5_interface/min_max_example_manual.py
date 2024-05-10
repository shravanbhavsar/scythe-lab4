#!/usr/bin/env python
###############################################################################
# Top contributors (to current version):
#   Yoni Zohar, Aina Niemetz, Andrew Reynolds
#
# This file is part of the cvc5 project.
#
# Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
# in the top-level source directory and their institutional affiliations.
# All rights reserved.  See the file COPYING in the top-level source
# directory for licensing information.
# #############################################################################
#
# A simple demonstration of the solving capabilities of the cvc5 sygus solver
# through the Python API. This is a direct translation of sygus-fun.cpp.
##

import copy
import cvc5
from pprint import pprint
# import utils
from cvc5 import Kind

if __name__ == "__main__":
    slv = cvc5.Solver()

    # required options
    slv.setOption("sygus", "true")
    slv.setOption("incremental", "false")

    # set the logic
    slv.setLogic("LIA")

    integer = slv.getIntegerSort()
    boolean = slv.getBooleanSort()

    # declare input variables for the functions-to-synthesize
    x = slv.mkVar(integer, "x")
    y = slv.mkVar(integer, "y")
    z = slv.mkVar(integer, "z")

    # declare the grammar non-terminals
    start = slv.mkVar(integer, "Start")
    start_bool = slv.mkVar(boolean, "StartBool")

    # define the rules
    zero = slv.mkInteger(0)
    one = slv.mkInteger(1)

    plus = slv.mkTerm(Kind.ADD, start, start)
    minus = slv.mkTerm(Kind.SUB, start, start)
    ite = slv.mkTerm(Kind.ITE, start_bool, start, start)

    And = slv.mkTerm(Kind.AND, start_bool, start_bool)
    Or = slv.mkTerm(Kind.OR, start_bool, start_bool)
    Not = slv.mkTerm(Kind.NOT, start_bool)
    leq = slv.mkTerm(Kind.LEQ, start, start)
    eq = slv.mkTerm(Kind.EQUAL, start, start)

    # create the grammar object
    g = slv.mkGrammar([x, y], [start, start_bool])

    # bind each non-terminal to its rules
    g.addRules(start, [zero, one, x, y, plus, minus, ite])
    g.addRules(start_bool, [And, Not, leq])

    # declare the functions-to-synthesize. Optionally, provide the grammar
    # constraints
    max2 = slv.synthFun("max", [x, y], integer, g)
    min2 = slv.synthFun("min", [x, y], integer)
    # declare universal variables.
    varX = slv.declareSygusVar("x", integer)
    varY = slv.declareSygusVar("y", integer)
    varZ = slv.declareSygusVar("z", integer)

    max_x_y = slv.mkTerm(Kind.APPLY_UF, max2, varX, varY)
    min_x_y = slv.mkTerm(Kind.APPLY_UF, min2, varX, varY)

    # add semantic constraints
    # (constraint (>= (max x y) x))
    slv.addSygusConstraint(slv.mkTerm(Kind.GEQ, max_x_y, varX))

    # (constraint (>= (max x y) y))
    slv.addSygusConstraint(slv.mkTerm(Kind.GEQ, max_x_y, varY))

    # (constraint (or (= x (max x y))
    #                 (= y (max x y))))
    slv.addSygusConstraint(slv.mkTerm(
        Kind.OR,
        slv.mkTerm(Kind.EQUAL, max_x_y, varX),
        slv.mkTerm(Kind.EQUAL, max_x_y, varY)))
    
    slv.addSygusConstraint(slv.mkTerm(Kind.LEQ, min_x_y, varX))
    slv.addSygusConstraint(slv.mkTerm(Kind.LEQ, min_x_y, varY))
    slv.addSygusConstraint(slv.mkTerm(
        Kind.OR,
        slv.mkTerm(Kind.EQUAL, min_x_y, varX),
        slv.mkTerm(Kind.EQUAL, min_x_y, varY)))
    

    # Add new function

    g_boolfn = slv.mkGrammar([x, y, z], [start_bool, start])
    g_boolfn.addRules(start, [x, y, z])
    g_boolfn.addRules(start_bool, [And, Or, Not, leq, eq])
    ismin = slv.synthFun("ismin", [x, y, z], boolean, g_boolfn)
    ismin_x_y_z = slv.mkTerm(Kind.APPLY_UF, ismin, varX, varY, varZ)
    consequences1 = slv.mkTerm(Kind.OR, slv.mkTerm(Kind.EQUAL, varX, varZ), slv.mkTerm(Kind.EQUAL, varY, varZ))
    slv.addSygusConstraint(slv.mkTerm(Kind.EQUAL, ismin_x_y_z, consequences1))



    # print solutions if available
    if (slv.checkSynth().hasSolution()):
        # Output should be equivalent to:
        # (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
        # (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
        terms = [max2, min2, ismin]
        pprint(slv.getSynthSolutions(terms))
    else:
        print("Failed to find a solution.")