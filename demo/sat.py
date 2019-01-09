import z3

def infer_rule(data, change_rule, feature_sizes):
  triples_changed = []
  for (l, c, r), new_c in data:
    changed_c = apply_change(c, change_rule)
    if changed_c !=  c:
      triples_changed.append(((l, c, r), c != new_c))
  rule = query_z3(triples_changed, feature_sizes)
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

def apply_change(features, rule):
  new_features = dict(features)
  new_features.update(rule)
  return new_features

def infer_change(pairs):
  solver = z3.Optimize()
  included_features = {}
  positive_features = {}
  for old, new in pairs:
    conjunction = []
    for feature, value in old.items():
      control_included = z3.Bool(f'|{feature} included|')
      control_positive = z3.Bool(f'|{feature} positive|')
      input_included = value != '0'
      input_positive = value == '+'
      output_included = new[feature] != '0'
      output_positive = new[feature] == '+'

      included_features[control_included] = feature
      positive_features[feature] = control_positive

      conjunction.append(z3.If(
        z3.And(control_included, input_included),
        z3.And(output_included == control_included, output_positive == control_positive),
        z3.And(output_included == input_included, output_positive == input_positive)
      ))
    solver.add(z3.And(*conjunction))

  for var in included_features.keys():
    solver.add_soft(z3.Not(var))

  if solver.check() == z3.sat:
    rule = {}
    model = solver.model()
    for ident, feature in included_features.items():
      if model[ident]:
        positive_feature = positive_features[feature]
        rule[feature] = '+' if model[positive_feature] else '-'
    return rule
  else:
    print('unsat')
    
    
def query_z3(triples_changed, feature_sizes):
  shared = shared_features([triple for triple, changed in triples_changed if changed])
  idents_to_features = {to_ident(feature, position): (feature, position) for feature, position in shared.keys()}
  
  solver = z3.Optimize()

  soft_assertions = []
  position_weights = {
    'left': 1000,
    'center': 0,
    'right': 1000
  }
  for control_included, (feature, position) in idents_to_features.items():
    # We use 10000 so that including new features is much worse than using more specific features.
    weight = 10000 + position_weights[position] + feature_sizes[(feature, shared[(feature, position)])]
    solver.add_soft(z3.Not(z3.Bool(control_included)), weight = weight)

  for triple, changed in triples_changed:
    conjunction = []
    for i, phone in enumerate(triple):
      for feature in phone.keys():
        position = POSITIONS[i]
        if (feature, position) in shared:
          control_included = z3.Bool(to_ident(feature, position))
          control_positive = shared[(feature, position)] == '+'
          input_included = phone[feature] != '0'
          input_positive = phone[feature] == '+'
          conjunction.append(z3.Implies(z3.And(control_included, input_included),
                                        control_positive == input_positive))
    if conjunction != []:
      solver.add(z3.And(*conjunction) == changed)

  if solver.check() == z3.sat:
    rule = (dict(), dict(), dict())
    model = solver.model()
    for ident in model:
      if z3.is_true(model[ident]):
        feature, position = idents_to_features[str(ident)]
        rule[POSITIONS.index(position)][feature] = shared[(feature, position)]
    return rule
  else:
    print('unsat')

