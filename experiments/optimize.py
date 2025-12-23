from z3 import *

# Create optimizer
opt = Optimize()

# Variables
x = Int('x')   # number of optional tasks
d = Int('d')   # deviation from preferred start time

# Basic constraints
opt.add(x >= 0, x <= 3)
opt.add(d >= 0)

# Tradeoff constraint:
# If x is small, deviation must be large
# (purely artificial, for illustration)
opt.add(d >= 10 - 3*x)

# Lexicographic optimization
opt.minimize(x)   # primary objective
opt.minimize(d)   # secondary objective

# Solve
if opt.check() == sat:
    model = opt.model()
    print("Solution:")
    print("x =", model[x])
    print("d =", model[d])
else:
    print("UNSAT")
