
from z3 import *  # @UnusedWildImport


AstRef.__invert__ = Not
AstRef.__rshift__ = Implies
AstRef.__or__ = Or
AstRef.__and__ = And


J = DeclareSort("J")
R = RealSort()
B = BoolSort()

i = Const("i", J)
j = Const("j", J)
k = Const("k", J)
th = Function("th", J, J, R)
th_def = Function("th_def", J, J, B)

J0 = Function("J0", J, B)
lt = Function("<", J, J, B)

th_def_r = lambda i, j: J0(i) & J0(j) & th_def(i,j)

assumptions = [
    ForAll([i, j, k], lt(i,j) >> (lt(j,k) >> lt(i,k))),    # Transitivity
    ForAll([i, j], ~lt(i,i) & (lt(i,j) >> ~lt(j,i))),      # anti-refl, anti-symm
    ForAll([i, j], th_def(i,j) >> lt(i, j)),               # type of th
    ForAll([i, j], J0(i) >> (~J0(j) >> lt(i,j)))           # J0 < J1
    ]

goals = [
    ForAll([k,j], J0(j) >> (th_def(k,j) == th_def_r(k,j)))
    ]

s = Solver()

for a in assumptions:
    print " *", a
    s.add(a)
    
for g in goals:
    print '-' * 80
    print " ?", g
    s.push()
    s.add(~g)
    check = s.check()
    if check == sat:
        print "invalid"
        print s.model()
    else:
        print "valid"
    s.pop()
    