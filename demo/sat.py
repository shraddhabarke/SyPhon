import z3

def infer_rule(data):
  triples_changed = [((l, c, r), c != new_c) for (l, c, r), new_c in data]
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
      features |= {((feature, POSITIONS[i]), value) for feature, value in phone.items()}
    if shared == None:
      shared = features
    else:
      shared &= features
  return dict(shared)
        
def query_z3(triples_changed):
  shared = shared_features([triple for triple, changed in triples_changed if changed])
  idents_to_features = {to_ident(feature, position): (feature, position) for feature, position in shared.keys()}

  solver = z3.Optimize()

  soft_assertions = []
  for ident in idents_to_features.keys():
    solver.add_soft(z3.Not(z3.Bool(ident)))

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
    print(model)
    for ident in model:
      print(str(ident))
      if z3.is_true(model[ident]):
        feature, position = idents_to_features[str(ident)]
        rule[POSITIONS.index(position)][feature] = shared[(feature, position)]
    return rule

