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
      feature_included = z3.Bool(f'|{feature} included|')
      feature_positive = z3.Bool(f'|{feature} positive|')
      included_features[feature_included] = feature
      positive_features[feature] = feature_positive
      conjunction.append(z3.If(
        z3.And(feature_included, value != '0'),
        feature_positive == (new[feature] == '+'),
        new[feature] == value
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
  for ident, (feature, position) in idents_to_features.items():
    solver.add_soft(z3.Not(z3.Bool(ident)), weight=10000 + position_weights[position] + feature_sizes[(feature, shared[(feature, position)])])

  for triple, changed in triples_changed:
    conjunction = []
    for i, phone in enumerate(triple):
      for feature in phone.keys():
        position = POSITIONS[i]
        if (feature, position) in shared:
          ident = to_ident(feature, position)
          included = phone[feature] != '0'
          matches = phone[feature] == shared[(feature, position)]
          conjunction.append(z3.Implies(z3.And(z3.Bool(ident), included), matches))
    if conjunction != []:
      if changed:
        solver.add(z3.And(*conjunction))
      else:
        solver.add(z3.Not(z3.And(*conjunction)))

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

