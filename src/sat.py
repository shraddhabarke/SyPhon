from . import ipa_data
from itertools import product
import z3, unicodedata, sys

IDENT = 0
def fresh():
  global IDENT
  IDENT += 1
  return 'formula' + str(IDENT)

def infer_rule(data):
  triples_changed = []
  for (l, c, r), new_c in data:
    if c == new_c:
      triples_changed.append(((l, c, r), False))
    else:
      triples_changed.append(((l, c, r), True))
  rule = infer_condition(triples_changed)
  return rule

POSITIONS = ['left', 'center', 'right']
POSITION_WEIGHTS = {
  'left': 2,
  'center': 1,
  'right': 2
}
NONEMPTY_WEIGHT = 100

LIKELIHOOD_WEIGHT = 1
SIMPLICITY_WEIGHT = 1000

def to_ident(feature, position):
  return f'|{feature} {position}|'

def shared_features(triples):
  shared = None
  for triple in triples:
    features = set()
    for i, phone in enumerate(triple):
      features |= {((feature, POSITIONS[i]), value) for feature, value in phone.items() if value != '0'}
    if shared == None:
      shared = features
    else:
      shared &= features
  return dict(shared)

def infer_change(change_vsa):
  opt = z3.Optimize()

  output = {}
  idents_to_changes = {}

  complete_change = {}
  simplified_change = {}

  for feature, values in change_vsa.changes.items():
    for value in values:
      idents_to_changes[f'input {feature} {value}'] = (feature, value)
      if feature not in output:
        output[feature] = []
      output[feature].append(f'input {feature} {value}')

      if value in {'+', '-', '0'}:
        opt.add_soft(z3.Not(z3.Bool(f'input {feature} {value}')))
      elif value != '0':
        opt.add_soft(z3.Not(z3.Bool(f'input {feature} {value}')), weight=2)

  for (feature1, values1), (feature2, values2) in product(change_vsa.changes.items(), repeat = 2):
    for value1, value2 in product(values1, values2):
      if value1 in {'+', '-'} and value2 in {'+', '-'}:
        if ipa_data.implies(feature1, value1, feature2, value2):
          output[feature2].append(f'input {feature1} {value1}')

  for feature, explanations in output.items():
    if feature in change_vsa.necessary_features:
      disjunction = []
      for explanation in explanations:
        disjunction.append(z3.Bool(explanation))
      opt.add(z3.Or(*disjunction))

  if opt.check() == z3.sat:
    model = opt.model()
    for ident in model:
      if str(ident) in idents_to_changes and model[ident]:
        feature, value = idents_to_changes[str(ident)]
        if value != '0':
          simplified_change[feature] = value
        complete_change[feature] = value
        for implied_feature, implied_value in ipa_data.get_implied(feature, value):
          complete_change[implied_feature] = implied_value
    return complete_change, simplified_change
  else:
    print('Change is unsat, this should never happen')

# def infer_change(old, new):
#   solver = z3.Optimize()
#   negative_features = {}
#   positive_features = {}
#   vars_to_features = {}

#   for feature, value in old.items():
#     control_negative = z3.Bool(f'|{feature} negative|')
#     control_positive = z3.Bool(f'|{feature} positive|')
#     input_negative = value == '-'
#     input_positive = value == '+'
#     output_negative = new[feature] == '-'
#     output_positive = new[feature] == '+'
#     vars_to_features[control_negative] = (feature, '-')
#     vars_to_features[control_positive] = (feature, '+')

#     negative_features[feature] = control_negative
#     positive_features[feature] = control_positive

#     positive_explanations = []
#     for implying_feature, implying_value in ipa_data.get_implying(feature, '+'):
#       implying_negative = z3.Bool(f'|{implying_feature} negative|')
#       implying_positive = z3.Bool(f'|{implying_feature} positive|')
#       if implying_value == '+':
#         positive_explanations.append(implying_positive)
#       elif implying_value == '-':
#         positive_explanations.append(implying_negative)

#     negative_explanations = []
#     for implying_feature, implying_value in ipa_data.get_implying(feature, '-'):
#       implying_negative = z3.Bool(f'|{implying_feature} negative|')
#       implying_positive = z3.Bool(f'|{implying_feature} positive|')
#       if implying_value == '+':
#         negative_explanations.append(implying_positive)
#       elif implying_value == '-':
#         negative_explanations.append(implying_negative)

#     solver.add(z3.Implies(control_negative, output_negative))
#     solver.add(z3.Implies(control_positive, output_positive))
#     solver.add(z3.Implies(output_negative, z3.Or(input_negative, control_negative, *negative_explanations)))
#     solver.add(z3.Implies(output_positive, z3.Or(input_positive, control_positive, *positive_explanations)))

#   for var in negative_features.values():
#     solver.add_soft(z3.Not(var))

#   for var in positive_features.values():
#     solver.add_soft(z3.Not(var))

#   if solver.check() == z3.sat:
#     rule = {}
#     model = solver.model()
#     for ident, (feature, val) in vars_to_features.items():
#       if model[ident]:
#         rule[feature] = val
#     return rule
#   else:
#     print('unsat')

def lookup(triple, feature, position):
  phone = triple[POSITIONS.index(position)]
  if feature in phone:
    return phone[feature]
  else:
    return '0'

def infer_assimilations(triples, features):
  solver = z3.Solver()
  candidate_assimilations = {feature: {'left', 'right'} for feature in features}

  for (l, c, r) in triples:
    for feature in features:
      if l[feature] != c[feature]:
        candidate_assimilations[feature].discard('left')
      if r[feature] != c[feature]:
        candidate_assimilations[feature].discard('right')

  return candidate_assimilations
    
def infer_condition(triples_changed):
  opt = z3.Optimize()
  solver = z3.Solver()

  for constraint in LIKELIHOOD_CONSTRAINTS | SIMPLICITY_CONSTRAINTS:
    opt.add(constraint)

  likelihood_formula = 0
  for cost in LIKELIHOOD_COSTS:
    likelihood_formula = cost + likelihood_formula
  likelihood = z3.Int('likelihood')
  opt.add(likelihood == likelihood_formula)

  simplicity_formula = 0
  for cost in SIMPLICITY_COSTS:
    simplicity_formula = cost + simplicity_formula
  simplicity = z3.Int('simplicity')
  opt.add(simplicity == simplicity_formula)

  n = len(triples_changed)
  n_pos = len([triple for triple, changed in triples_changed if changed])
  n_neg = len([triple for triple, changed in triples_changed if not changed])

  objective_formula = likelihood * LIKELIHOOD_WEIGHT * n + simplicity * SIMPLICITY_WEIGHT
  objective = z3.Int('objective')
  opt.add(objective == objective_formula)
  opt.minimize(objective)

  formulas = {}
  for triple, changed in triples_changed:
    conjunction = []
    for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
      ident = z3.Bool(f'{feature} {position} {value}')
      if lookup(triple, feature, position) != value:
        conjunction.append(z3.Not(ident))
    name = fresh()
    assertion = z3.And(*conjunction) == changed
    formulas[name] = (assertion, triple, changed)
    opt.add(assertion)
    solver.assert_and_track(assertion, name)

  # for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
  #   if feature == 'sonorant' and position == 'right' and value == '-':
  #     opt.add(z3.Bool(f'sonorant right -'))
  #     solver.assert_and_track(z3.Bool(f'sonorant right -'), f'force hungarian sonorant right -')
  #   else:
  #     opt.add(z3.Not(z3.Bool(f'{feature} {position} {value}')))
  #     solver.assert_and_track(z3.Not(z3.Bool(f'{feature} {position} {value}')), f'force hungarian not {feature} {position} {value}')

  #force_assimilation = z3.Or(z3.Bool('voice right +'), z3.Bool('voice right -'))
  #formulas['assimilation'] = (force_assimilation, ({}, {'voicing': 'assimilation'}, {}), False)
  #opt.add(force_assimilation)
  #solver.assert_and_track(force_assimilation, 'assimilation')
  i = 0
  if True:
    i += 1
    if opt.check() == z3.sat:
      rule = ({}, {}, {})
      model = opt.model()
      new_model_constraint = []
      for ident in model:
        if str(ident) in IDENTS_TO_FEATURES and model[ident]:
          feature, position, value = IDENTS_TO_FEATURES[str(ident)]
          rule[POSITIONS.index(position)][feature] = value
          new_model_constraint.append(z3.Bool(str(ident)))
      # print(f'#{i}')
      print(f'Rule: {rule}')
      print(f'N: {n}')
      print(f'N+: {n_pos}')
      print(f'N-: {n_neg}')
      print(f'Simplicity weight: {SIMPLICITY_WEIGHT}')
      print(f'Likelihood weight: {LIKELIHOOD_WEIGHT}')
      print(f'Objective: {model[objective]}')
      print(f'Simplicity score: {model[simplicity]}')
      print(f'Simplicity: {model[simplicity].as_long() * SIMPLICITY_WEIGHT}')
      print(f'Likelihood score: {model[likelihood]}')
      print(f'Likelihood: {model[likelihood].as_long() * LIKELIHOOD_WEIGHT * n}')
      return rule
      opt.add(z3.Not(z3.And(*new_model_constraint)))
    else:
      solver.check()
      unsat_core = solver.unsat_core()
      print('\033[1;31mUnsatisfiable constraints:\033[0;31m') # Set text color to red
      for name in unsat_core:
        if str(name) in formulas:
          formula, (l, c, r), changed = formulas[str(name)]
          changed_str = 'changed' if changed else "didn't change"
          print(f'/{l} . {c} . {r}/ {changed_str}')
        else:
          print(f'{str(name)}')
      print('\033[0;0m') # Reset text color and add a newline
      return None
      #return None
  print('')

LIKELIHOOD_COSTS = set()
LIKELIHOOD_CONSTRAINTS = set()

def calc_likelihood():
  global LIKELIHOOD_COSTS, LIKELIHOOD_CONSTRAINTS
  def to_constraint(feature, position, value):
    plus = z3.Bool(f'{feature} {position} +')
    minus = z3.Bool(f'{feature} {position} -')
    if value == '+':
      return minus
    elif value == '-':
      return plus
    else:
      return z3.Or(plus, minus)

  for letter, features in ipa_data.LETTERS_TO_FEATURES.items():
    letter_name = []
    for char in letter:
      letter_name.append(unicodedata.name(char))

    for position in POSITIONS:
      disjunction = set()
      for feature in ipa_data.FEATURES:
        disjunction.add(to_constraint(feature, position, features[feature]))

      cost = z3.Int(f'likelihood cost {letter_name} {position}')
      cost_fn = z3.If(z3.Or(*disjunction), 0, 1)
      LIKELIHOOD_COSTS.add(cost)
      LIKELIHOOD_CONSTRAINTS.add(cost == cost_fn)

  LIKELIHOOD_COSTS = frozenset(LIKELIHOOD_COSTS)
  LIKELIHOOD_CONSTRAINTS = frozenset(LIKELIHOOD_CONSTRAINTS)

SIMPLICITY_COSTS = set()
SIMPLICITY_CONSTRAINTS = set()

def calc_simplicity():
  global SIMPLICITY_COSTS, SIMPLICITY_CONSTRAINTS

  for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
    nonempty = z3.Bool(f'{position} nonempty')
    ident = z3.Bool(f'{feature} {position} {value}')
    weight = POSITION_WEIGHTS[position]
    cost = z3.Int(f'simplicity cost {feature} {position} {value}')
    cost_fn = z3.If(ident, weight, 0)
    SIMPLICITY_COSTS.add(cost)
    SIMPLICITY_CONSTRAINTS.add(z3.Implies(ident, nonempty))
    SIMPLICITY_CONSTRAINTS.add(cost == cost_fn)
  SIMPLICITY_COSTS.add(z3.If(z3.Bool('left nonempty'), NONEMPTY_WEIGHT, 0))
  SIMPLICITY_COSTS.add(z3.If(z3.Bool('right nonempty'), NONEMPTY_WEIGHT, 0))
  SIMPLICITY_COSTS = frozenset(SIMPLICITY_COSTS)
  SIMPLICITY_CONSTRAINTS = frozenset(SIMPLICITY_CONSTRAINTS)

IDENTS_TO_FEATURES = {}
def calc_idents_to_features():
  global IDENTS_TO_FEATURES
  for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
    ident = f'{feature} {position} {value}'
    IDENTS_TO_FEATURES[ident] = (feature, position, value)

def init():
  calc_likelihood()
  calc_simplicity()
  calc_idents_to_features()

init()
