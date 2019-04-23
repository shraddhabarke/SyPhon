from . import ipa_data
import z3

IDENT = 0
def get_ident():
  global IDENT
  IDENT += 1
  return 'formula' + str(IDENT)

def infer_rule(data):
  triples_changed = []
  for (l, c, r), new_c in data:
    triples_changed.append(((l, c, r), c != new_c))
  rule = query_z3(triples_changed)
  return rule

POSITIONS = ['left', 'center', 'right']

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

    zero_explanations = []
    for implying_feature, implying_value in ipa_data.get_implying(feature, '0'):
      implying_negative = z3.Bool(f'|{implying_feature} negative|')
      implying_positive = z3.Bool(f'|{implying_feature} positive|')
      if implying_value == '+':
        zero_explanations.append(implying_positive)
      elif implying_value == '-':
        zero_explanations.append(implying_negative)

    solver.add(z3.Implies(control_negative, output_negative))
    solver.add(z3.Implies(control_positive, output_positive))
    solver.add(z3.Implies(input_negative, z3.Or(output_negative, control_positive, *positive_explanations, *zero_explanations)))
    solver.add(z3.Implies(input_positive, z3.Or(output_positive, control_negative, *negative_explanations, *zero_explanations)))

    solver.add(z3.Not(z3.And(control_negative, control_positive)))

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
    
    
def query_z3(triples_changed):
  shared = shared_features([triple for triple, changed in triples_changed if changed])
  idents_to_features = {to_ident(feature, position): (feature, position) for feature, position in shared.keys()}
  
  opt = z3.Optimize()
  solver = z3.Solver()
  solver.set(unsat_core=True)
  formulas = {}

  soft_assertions = []
  position_weights = {
    'left': 20000,
    'center': 10000,
    'right': 20000
  }
  for control_included, (feature, position) in idents_to_features.items():
    # # We use 10000 so that including new features is much worse than using more specific features.
    # weight = 10000 + position_weights[position] + ipa_data.get_weight(feature, shared[(feature, position)])
    opt.add_soft(z3.Not(z3.Bool(control_included)), weight = position_weights[position])

  print(ipa_data.FEATURE_WEIGHTS)
  for (feature, position), value in shared.items():
    control_included = z3.Bool(to_ident(feature, position))
    control_positive = shared[(feature, position)] == '+'
    input_included = value != '0'
    input_positive = value == '+'
    weight = ipa_data.get_weight(feature, value)
    print((feature, value, position, weight))
    opt.add_soft(z3.Not(z3.And(control_included, input_included, control_positive == input_positive)), weight = weight)

  for triple, changed in triples_changed:
    conjunction = []
    for i, phone in enumerate(triple):
      for feature in ipa_data.FEATURES:
        position = POSITIONS[i]
        if (feature, position) in shared:
          control_included = z3.Bool(to_ident(feature, position))
          control_positive = shared[(feature, position)] == '+'
          input_included = phone[feature] != '0' if feature in phone else False
          input_positive = phone[feature] == '+' if feature in phone else False
          conjunction.append(z3.Implies(control_included, z3.And(input_included, control_positive == input_positive)))
    formula = z3.And(*conjunction) == changed
    opt.assert_exprs(formula)
    name = z3.Bool(get_ident())
    formulas[name] = (formula, triple, changed)
    solver.assert_and_track(formula, name)


  if opt.check() == z3.sat:
    rule = ({}, {}, {})
    model = opt.model()
    for ident in model:
      if model[ident]:
        feature, position = idents_to_features[str(ident)]
        rule[POSITIONS.index(position)][feature] = shared[(feature, position)]
    return rule
  else:
    solver.check()
    unsat_core = solver.unsat_core()
    print('Unsat core:')
    for name in unsat_core:
      formula, (l, c, r), changed = formulas[name]
      print('Formula:')
      print(formula)
      print('Left:')
      print(ipa_data.FEATURES_TO_SYMBOLS.get(frozenset(l.items()), l))
      print('Center:')
      print(ipa_data.FEATURES_TO_SYMBOLS.get(frozenset(c.items()), c))
      print('Right:')
      print(ipa_data.FEATURES_TO_SYMBOLS.get(frozenset(r.items()), r))
      print('Changed:')
      print(changed)
      print(formulas[name])
    print('Shared:')
    print(shared)
    return None
