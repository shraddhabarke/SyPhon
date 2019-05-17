import itertools
from . import ipa_data, parse_ipa, sat
from .change import Change, ChangeVsa

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

def intersect_assimilations(assimilations_1, assimilations_2):
  if assimilations_1.keys() != assimilations_2.keys():
    return None

  new_assimilation = {}
  for feature, positions in assimilations_1.items():
    new_positions = positions & assimilations_2[feature]
    if not new_positions:
      return None
    new_assimilation[feature] = new_positions

  return new_positions

def merge(change_1, data_1, change_2, data_2):
  replacement_1, assimilations_1 = change_1
  replacement_2, assimilations_2 = change_2

  if change_1 == change_2:
    return (change_1, [*data_1, *data_2])
  elif replacement_1 == replacement_2:
    new_assimilations = intersect_assimilations(assimilations_1, assimilations_2)
    if new_assimilations:
      return ((replacement_1, new_assimilations), [*data_1, *data_2])
    else:
      return None
  elif replacement_1.keys() == replacement_2.keys():
    new_replacement = {}
    alpha_features = set()
    for feature in replacement_1.keys():
      if feature in replacement_1 and feature in replacement_2 and replacement_1[feature] != replacement_2[feature]:
        new_replacement[feature] = 'alpha'
      else:
        new_replacement[feature] = replacement_1[feature]

    for feature, value in new_replacement.items():
      if value == 'alpha':
        alpha_features.add(feature)

    new_data = [*data_1, *data_2]
    assimilation_data = [(l, new_c, r) for (l, c, r), new_c in new_data]
    new_assimilations = sat.infer_assimilations(assimilation_data, alpha_features)

    if not alpha_features or new_assimilations:
      return ((new_replacement, new_assimilations), new_data)
    else:
      return None

# def infer_change(data):
#   changed = [((l, old, r), new) for (l, old, r), new in data if old != new]
#   changes = [((sat.infer_change(old, new), set()), [((l, old, r), new)]) for (l, old, r), new in changed]
#   merged_changes = []
#   for change, data_1 in changes:
#     merged = False
#     for i, (merged_change, data_2) in enumerate(merged_changes):
#       new_change = merge(change, data_1, merged_change, data_2)
#       if new_change:
#         merged = True
#         merged_changes[i] = new_change
#         break
#     if not merged:
#       merged_changes.append((change, data_1))
#   return merged_changes

def infer_change(data):
  change_vsas = []
  for ((l, old, r), new) in data:
    if old == new:
      continue

    context = {
      'left': l,
      'right': r
    }
    change_vsa = ChangeVsa(old, new, context)

    for i, other_change_vsa in enumerate(change_vsas):
      merged_change_vsa = change_vsa & other_change_vsa
      if merged_change_vsa:
        change_vsas[i] = merged_change_vsa
        break
    else:
      change_vsas.append(change_vsa)
  return [change_vsa.to_change() for change_vsa in change_vsas]


def infer_rule(data, changes):
  rules = []
  for change in changes:
    subdata = []
    for (l, c, r), new_c in data:
      changed_c = change.apply(c, {'left': l, 'right': r})
      # changed_c = c.copy()
      # for feature, value in concrete_change.items():
      #   if value in {'+', '-', '0'}:
      #     changed_c[feature] = value
      #   elif value == 'left':
      #     changed_c[feature] = l[feature]
      #   elif value == 'right':
      #     changed_c[feature] = r[feature]
      #   else:
      #     print('oh no')
      # # if (l, c, r) == (context['left'], old, context['right']):
      # #   print('Triple:')
      # #   print((l, c, r))
      # #   print('Old:')
      # #   print(c)
      # #   print('Changed:')
      # #   print(changed_c)
      # #   print('New:')
      # #   print(new_c)
      # #   print('Difference:')
      # #   for feature, value in changed_c.items():
      # #     if new_c[feature] != value:
      # #       print(f'changed {value}{feature} vs. new {new_c[feature]}{feature}')
      # # Whyyy no positive examples
      if changed_c == new_c and changed_c != c:
        subdata.append(((l, c, r), True))
      elif changed_c != new_c:
        subdata.append(((l, c, r), False))
    inferred_rule = sat.infer_condition(subdata)
    if inferred_rule:
      rules.append((change, inferred_rule))
    else:
      rules.append(None)
  return rules
