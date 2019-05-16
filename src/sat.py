import ipa_data
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
    triples_changed.append(((l, c, r), c != new_c))
  rule = infer_condition(triples_changed)
  return rule

POSITIONS = ['left', 'center', 'right']
POSITION_WEIGHTS = {
  'left': 2,
  'center': 1,
  'right': 2
}

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

def infer_change(old, new):
  solver = z3.Optimize()
  negative_features = {}
  positive_features = {}
  vars_to_features = {}
  for feature, value in old.items():
    control_negative = z3.Bool(f'|{feature} negative|')
    control_positive = z3.Bool(f'|{feature} positive|')
    input_negative = value == '-'
    input_positive = value == '+'
    output_negative = new[feature] == '-'
    output_positive = new[feature] == '+'
    vars_to_features[control_negative] = (feature, '-')
    vars_to_features[control_positive] = (feature, '+')

    negative_features[feature] = control_negative
    positive_features[feature] = control_positive

    positive_explanations = []
    for implying_feature, implying_value in ipa_data.get_implying(feature, '+'):
      implying_negative = z3.Bool(f'|{implying_feature} negative|')
      implying_positive = z3.Bool(f'|{implying_feature} positive|')
      if implying_value == '+':
        positive_explanations.append(implying_positive)
      elif implying_value == '-':
        positive_explanations.append(implying_negative)

    negative_explanations = []
    for implying_feature, implying_value in ipa_data.get_implying(feature, '-'):
      implying_negative = z3.Bool(f'|{implying_feature} negative|')
      implying_positive = z3.Bool(f'|{implying_feature} positive|')
      if implying_value == '+':
        negative_explanations.append(implying_positive)
      elif implying_value == '-':
        negative_explanations.append(implying_negative)

    solver.add(z3.Implies(control_negative, output_negative))
    solver.add(z3.Implies(control_positive, output_positive))
    solver.add(z3.Implies(output_negative, z3.Or(input_negative, control_negative, *negative_explanations)))
    solver.add(z3.Implies(output_positive, z3.Or(input_positive, control_positive, *positive_explanations)))

  for var in negative_features.values():
    solver.add_soft(z3.Not(var))

  for var in positive_features.values():
    solver.add_soft(z3.Not(var))

  if solver.check() == z3.sat:
    rule = {}
    model = solver.model()
    for ident, (feature, val) in vars_to_features.items():
      if model[ident]:
        rule[feature] = val
    return rule
  else:
    print('unsat')

def lookup(triple, feature, position):
  phone = triple[POSITIONS.index(position)]
  if feature in phone:
    return phone[feature]
  else:
    return '0'
    
def infer_condition(triples_changed):
  opt = z3.Optimize()
  solver = z3.Solver()

  for constraint in LIKELIHOOD_CONSTRAINTS | SIMPLICITY_CONSTRAINTS:
    opt.add(constraint)

  likelihood_objective_fn = 0
  for cost in LIKELIHOOD_COSTS:
    likelihood_objective_fn = cost + likelihood_objective_fn

  simplicity_objective_fn = 0
  for cost in SIMPLICITY_COSTS:
    simplicity_objective_fn = cost + simplicity_objective_fn

  objective_fn = likelihood_objective_fn * LIKELIHOOD_WEIGHT * len(triples_changed) + simplicity_objective_fn * SIMPLICITY_WEIGHT
  objective_fn_var = z3.Int('objective fn')
  opt.add(objective_fn_var == objective_fn)
  opt.minimize(objective_fn_var)

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

  if opt.check() == z3.sat:
    rule = ({}, {}, {})
    model = opt.model()
    for ident in model:
      if str(ident) in IDENTS_TO_FEATURES and model[ident]:
        feature, position, value = IDENTS_TO_FEATURES[str(ident)]
        rule[POSITIONS.index(position)][feature] = value
    return rule
  else:
    solver.check()
    unsat_core = solver.unsat_core()
    print('\033[1;31mUnsatisfiable constraints:\033[0;31m') # Set text color to red
    for name in unsat_core:
      formula, (l, c, r), changed = formulas[str(name)]
      changed_str = 'changed' if changed else "didn't change"
      print(f'/{l} . {c} . {r}/ {changed_str}')
    print('\033[0;0m') # Reset text color and add a newline
    return None

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
    ident = z3.Bool(f'{feature} {position} {value}')
    weight = POSITION_WEIGHTS[position]
    cost = z3.Int(f'simplicity cost {feature} {position} {value}')
    cost_fn = z3.If(ident, weight, 0)
    SIMPLICITY_COSTS.add(cost)
    SIMPLICITY_CONSTRAINTS.add(cost == cost_fn)
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
