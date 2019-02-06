import itertools
from . import ipa_data, parse_ipa, sat

def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

def parse(words):
  data = []
  for underlying_form, realization in words:
    underlying_features = parse_ipa.parse('#' + underlying_form + '#')
    realized_features = parse_ipa.parse(realization)
    for i, triple in enumerate(triples(underlying_features)):
      data.append((triple, realized_features[i]))
  return data

def infer_change(data):
  def try_merge(change1, change2):
    data1, rule1 = change1
    data2, rule2 = change2
    if rule1 == rule2:
      return ([*data1, *data2], rule1)
    else:
      merged_rule = {}
      for feature, value in rule1.items() | rule2.items():
        if feature in merged_rule:
          return None
        else:
          merged_rule[feature] = value
      merged_data = [*data1, *data2]
      for (old, new) in merged_data:
        if ipa_data.apply_change(merged_rule, old) != new:
          return None
      return (merged_data, merged_rule)

  changed = [(old, new) for (_, old, _), new in data if old != new]
  changes = [([(old, new)], sat.infer_change(old, new)) for old, new in changed]
  print([rule for data, rule in changes])
  merged_changes = []
  for change in changes:
    merged = False
    for i, merged_change in enumerate(merged_changes):
      new_change = try_merge(change, merged_change)
      if new_change != None:
        merged = True
        merged_changes[i] = new_change
        break
    if not merged:
      merged_changes.append(change)
  #print([rule for data, rule in merged_changes])
  return merged_changes

def infer_rule(data, change):
  rules = []
  changes = [pair for data, rule in change for pair in data]
  for change_data, rule in change:
    subdata = []
    for (l, c, r), new_c in data:
      if (c, new_c) in change_data:
        subdata.append(((l, c, r), new_c))
      elif (c, new_c) not in changes and c == new_c and ipa_data.apply_change(rule, c) != c:
        subdata.append(((l, c, r), new_c))
    inferred_rule = sat.infer_rule(subdata)
    if inferred_rule:
      rules.append((rule, inferred_rule))
    else:
      rules.append(None)
  return rules
