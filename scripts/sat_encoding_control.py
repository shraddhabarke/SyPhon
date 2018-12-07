# sat encoding with control
# to install z3: "pip3 install z3-solver"
import csv

from z3 import And, Or, Implies, Bool, Not, solve, Solver

examples = [
    ('+', '+', True),
    ('+', '-', True),
    ('+', '0', True),
    ('-', '+', False),
    ('-', '-', False),
    # ('0', '0', False),
]
feature_list = ['v', 's']

# uncomment the following part to try on real examples
# examples = []
# with open('../datasets/Russianriggle.csv') as f:
# with open('../datasets/Kikuriariggle.csv') as f:
#     f = csv.reader(f)
#     _, *feature_list = next(f)
#     for line in f:
#         triple, *features = line
#         if ('#' in features):  # ignore word endings for now TODO
#             continue
#         # the last column is target (1 means positive example; 0 means neg example)
#         example = features[:-1] + [features[-1] == '1']
#         examples.append(example)
#         print(triple, example)

encoded_examples = []
for example in examples:
    changed = example[-1]
    features = example[:-1]
    encoded_feature_req = []
    i = 0

    for fname, f in zip(feature_list, features):
        i += 1
        v_inc = Bool(fname + "_i'")
        v_pos = Bool(fname + "_p'")
        if f == '0':
            v_inc = Not(v_inc)
        if f == '-':
            v_pos = Not(v_pos)
        encoded_feature_req.append(
            Implies(And(Bool(fname), v_inc), v_pos)
        )

    c = And(encoded_feature_req)
    if not changed:
        c = Not(c)
    # print(c)
    encoded_examples.append(c)

# print(encoded_examples)
f = And(encoded_examples)
# print(f)
solver = Solver()
solver.set(unsat_core=True)
solver.add(f)
print(solver.check())
print(solver.model())

# find unsat core
for fname in feature_list:
    solver.assert_and_track(Not(Bool(fname)), Bool('not ' + fname))
    solver.assert_and_track(Bool(fname), Bool('is ' + fname))
print(solver.check())
print(solver.unsat_core())
