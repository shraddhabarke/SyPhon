import itertools
from demo import parse_ipa, sat

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
  changed = [(old, new) for (_, old, _), new in data if old != new]
  return sat.infer_change(changed)

def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule)
