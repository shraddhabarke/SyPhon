from phonosynthesis import ipa_data
from itertools import product
import z3, unicodedata, sys, math

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
FEATURE_PENALTY = 1000
FEATURE_SIMPLICITY_WEIGHT = 5
NONEMPTY_PENALTY = 50000

LIKELIHOOD_WEIGHT = 30
SIMPLICITY_WEIGHT = 1

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

  log_num_models = z3.Int('log # models')
  opt.add(log_num_models == LOG_NUM_MODELS)

  simplicity_formula = 0
  for cost in SIMPLICITY_COSTS:
    simplicity_formula = cost + simplicity_formula
  simplicity_score = z3.Int('simplicity score')
  opt.add(simplicity_score == simplicity_formula)

  n = len(triples_changed)
  n_pos = len([triple for triple, changed in triples_changed if changed])
  n_neg = len([triple for triple, changed in triples_changed if not changed])

  simplicity = z3.Int('simplicity')
  likelihood = z3.Int('likelihood')
  opt.add(simplicity == simplicity_score * SIMPLICITY_WEIGHT)
  opt.add(likelihood == log_num_models * LIKELIHOOD_WEIGHT * n_pos)

  objective = z3.Int('objective')
  opt.add(objective == simplicity + likelihood)
  opt.minimize(objective)

  alphas = {}
  formulas = {}
  for triple, changed in triples_changed:
    conjunction = []
    for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
      ident = z3.Bool(f'{feature} {position} {value}')
      if lookup(triple, feature, position) != value:
        conjunction.append(z3.Not(ident))
    for feature in ipa_data.FEATURES:
      alphas[f'alpha left right {feature}'] = (feature, {'left', 'right'})
      # alphas[f'alpha left center {feature}'] = (feature, {'left', 'center'})
      # alphas[f'alpha center right {feature}'] = (feature, {'center', 'right'})
      lval = lookup(triple, feature, 'left')
      rval = lookup(triple, feature, 'right')

      lr_ident = z3.Bool(f'alpha left right {feature}')
      if lval != rval or lval == '0' or rval == '0':
        conjunction.append(z3.Not(lr_ident))

    triple_changed = z3.And(*conjunction)
    name = fresh()
    assertion = triple_changed == changed
    formulas[name] = (assertion, triple, changed)
    opt.add(assertion)
    solver.assert_and_track(assertion, name)

  # deleted_must_have_context_constraint = []
  # for feature, value in product(ipa_data.FEATURES, ['+', '-']):
  #   if feature == 'deleted' and value == '+':
  #     deleted_must_have_context_constraint.append(z3.Bool(f'deleted center +'))
  #   else:
  #     for position in POSITIONS:
  #       deleted_must_have_context_constraint.append(z3.Not(z3.Bool(f'{feature} {position} {value}')))
  # opt.add(z3.Not(z3.And(*deleted_must_have_context_constraint)))
  # solver.assert_and_track(z3.Not(z3.And(*deleted_must_have_context_constraint)), 'deleted must have context')

  #opt.add(z3.Bool(f'alpha left right strident'))
  #solver.assert_and_track(z3.Bool(f'alpha left right s'), 'alrsonorant')

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
        elif str(ident) in alphas and model[ident]:
          feature, positions = alphas[str(ident)]
          for position in positions:
            rule[POSITIONS.index(position)][feature] = 'α'

      # print(f'#{i}')
      print(f'Rule: {rule}')
      print(f'N: {n}')
      print(f'N+: {n_pos}')
      print(f'N-: {n_neg}')
      print(f'Simplicity weight: {SIMPLICITY_WEIGHT}')
      print(f'Likelihood weight: {LIKELIHOOD_WEIGHT}')
      print(f'Objective: {model[objective]}')
      print(f'Simplicity score: {model[simplicity_score]}')
      print(f'Simplicity: {model[simplicity]}')
      print(f'Log # models: {model[log_num_models]}')
      print(f'Likelihood: {model[likelihood]}')
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

LOG_NUM_MODELS = 0
LIKELIHOOD_CONSTRAINTS = set()

def calc_likelihood():
  global LOG_NUM_MODELS, LIKELIHOOD_CONSTRAINTS
  def to_constraint(feature, position, value):
    plus = z3.Bool(f'{feature} {position} +')
    minus = z3.Bool(f'{feature} {position} -')
    alpha = z3.Bool(f'alpha left right {feature}')
    if value == '+':
      return minus
    elif value == '-':
      return plus
    else:
      if position in {'left', 'right'}:
        return z3.Or(plus, minus, alpha)
      else:
         return z3.Or(plus, minus)

  num_models = [1, 1, 1]
  for letter, features in ipa_data.LETTERS_TO_FEATURES.items():
    letter_name = []
    for char in letter:
      letter_name.append(unicodedata.name(char))

    for i, position in enumerate(POSITIONS):
      disjunction = set()
      for feature in ipa_data.FEATURES:
        disjunction.add(to_constraint(feature, position, features[feature]))

      in_model = z3.Int(f'in model {letter_name} {position}')
      in_model_fn = z3.If(z3.Or(*disjunction), 0, 1)
      num_models[i] = in_model + num_models[i]
      LIKELIHOOD_CONSTRAINTS.add(in_model == in_model_fn)

  for i, position in enumerate(POSITIONS):
    LIKELIHOOD_CONSTRAINTS.add(z3.Int(f'# models {position}') == num_models[i])
    LIKELIHOOD_CONSTRAINTS.add(z3.Int(f'# models {position}') <= len(ipa_data.LETTERS) + 1)

  for i in range(1, len(ipa_data.LETTERS) + 2):
    log_i = math.floor(100 * math.log(i))
    for j, position in enumerate(POSITIONS):
      LIKELIHOOD_CONSTRAINTS.add(z3.Implies(z3.Int(f'# models {position}') == i, z3.Int(f'log models {position}') == i))

  for i, position in enumerate(POSITIONS):
    LOG_NUM_MODELS = z3.Int(f'log models {position}') + LOG_NUM_MODELS

  LIKELIHOOD_CONSTRAINTS = frozenset(LIKELIHOOD_CONSTRAINTS)

SIMPLICITY_COSTS = set()
SIMPLICITY_CONSTRAINTS = set()

def calc_simplicity():
  global SIMPLICITY_COSTS, SIMPLICITY_CONSTRAINTS

  for feature in ipa_data.FEATURES:
    lr = z3.Bool(f'alpha left right {feature}')
    cost_lr = z3.Int(f'simplicity cost alpha left right {feature}')
    # lc = z3.Bool(f'alpha left center {feature}')
    # cost_lc = z3.Int(f'simplicity cost alpha left center {feature}')
    # cr = z3.Bool(f'alpha center right {feature}')
    # cost_cr = z3.Int(f'simplicity cost alpha center right {feature}')

    SIMPLICITY_CONSTRAINTS.add(z3.Implies(lr, z3.Bool('left nonempty')))
    SIMPLICITY_CONSTRAINTS.add(z3.Implies(lr, z3.Bool('right nonempty')))
    # SIMPLICITY_CONSTRAINTS.add(z3.Implies(lc, z3.Bool('left nonempty')))
    # SIMPLICITY_CONSTRAINTS.add(z3.Implies(cr, z3.Bool('right nonempty')))

    weight = 2 * (FEATURE_PENALTY + FEATURE_SIMPLICITY_WEIGHT * ipa_data.FEATURE_SIMPLICITY[feature])
    cost_fn_lr = z3.If(lr, weight, 0)
    SIMPLICITY_COSTS.add(cost_lr)
    SIMPLICITY_CONSTRAINTS.add(cost_lr == cost_fn_lr)
    # cost_fn_lc = z3.If(lc, weight, 0)
    # SIMPLICITY_COSTS.add(cost_lc)
    # SIMPLICITY_CONSTRAINTS.add(cost_lc == cost_fn_lc)
    # cost_fn_cr = z3.If(cr, weight, 0)
    # SIMPLICITY_COSTS.add(cost_cr)
    # SIMPLICITY_CONSTRAINTS.add(cost_cr == cost_fn_cr)

  for feature, position, value in product(ipa_data.FEATURES, POSITIONS, ['+', '-']):
    nonempty = z3.Bool(f'{position} nonempty')
    ident = z3.Bool(f'{feature} {position} {value}')
    weight = POSITION_WEIGHTS[position] * FEATURE_PENALTY + FEATURE_SIMPLICITY_WEIGHT * ipa_data.FEATURE_SIMPLICITY[feature]
    cost = z3.Int(f'simplicity cost {feature} {position} {value}')
    cost_fn = z3.If(ident, weight, 0)
    #print(f'{value}{feature} {position}: {weight}')
    SIMPLICITY_COSTS.add(cost)
    SIMPLICITY_CONSTRAINTS.add(z3.Implies(ident, nonempty))
    SIMPLICITY_CONSTRAINTS.add(cost == cost_fn)
  SIMPLICITY_COSTS.add(z3.If(z3.Bool('left nonempty'), NONEMPTY_PENALTY, 0))
  SIMPLICITY_COSTS.add(z3.If(z3.Bool('right nonempty'), NONEMPTY_PENALTY, 0))
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
