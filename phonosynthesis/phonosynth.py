import itertools
from phonosynthesis import ipa_data
from phonosynthesis import parse_ipa
from phonosynthesis import sat
from phonosynthesis.change import Change, ChangeVsa

def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

def parse(words):
  data = []
  for underlying_form, surface_form in words:
    underlying_phones = parse_ipa.parse('#' + underlying_form + '#')
    surface_phones = parse_ipa.parse('#' + surface_form + '#')

    if len(underlying_phones) != len(surface_phones):
      for phone in underlying_phones:
        print(f'underlying: {phone}')
      for phone in surface_phones:
        print(f'surface: {phone}')

    word = []
    for underlying_phone, surface_phone in zip(underlying_phones, surface_phones):
      word.append((underlying_phone, surface_phone))
   
    data.append(word)
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

  for word in data:
    word_iter = iter(word)
    target = next(word_iter)[0]
    right, next_surface = next(word_iter)

    for underlying_phone, surface_phone in iter(word):
      surface = next_surface
      next_surface = surface_phone

      left = target
      target = right
      right = underlying_phone

      if target != surface:
        change_vsa = ChangeVsa(target, surface, {'left': left, 'right': right})

        for i, other_change_vsa in enumerate(change_vsas):
          merged_change_vsa = change_vsa & other_change_vsa
          if merged_change_vsa:
            change_vsas[i] = merged_change_vsa
            break
        else:
          change_vsas.append(change_vsa)

  changes = [change_vsa.to_change() for change_vsa in change_vsas]
  return changes


def infer_rule(data, changes):
  rules = []

  while len(changes) > 0:
    for i, change in enumerate(changes):
      solver_data = []

      if change.is_insertion():
        target = ipa_data.get_empty_phone()

        for word in data:
          word_iter = iter(word)
          right = next(word_iter)[0]

          for underlying_phone, surface_phone in word_iter:
            left = right
            if underlying_phone['deleted'] == '+':
              changed = True
              right = next(word_iter)[0]
            else:
              changed = False
              right = underlying_phone
            solver_data.append(((left, target, right), changed))
      else:
        for word in data:
          word_iter = iter(word)
          target = next(word_iter)[0]
          right, next_surface = next(word_iter)

          for underlying_phone, surface_phone in word_iter:
            if underlying_phone['deleted'] == '+':
              continue

            surface = next_surface
            next_surface = surface_phone

            left = target
            target = right
            right = underlying_phone

            changed_target = change.apply(target, {'left': left, 'right': right})

            if changed_target == surface and changed_target != target:
              solver_data.append(((left, target, right), True))
            elif changed_target != surface:
              solver_data.append(((left, target, right), False))

      inferred_rule = sat.infer_condition(solver_data)
      if inferred_rule:
        changes.pop(i)
        rules.append((change, inferred_rule))
        break
    else:
      return rules + [None] # should really just be None but don't want to break Shraddha

    change, (left, target, right) = rules[-1]
    for i, word in enumerate(data):
      new_word = word.copy()
      for j, ((lu, ls), (tu, ts), (ru, rs)) in enumerate(triples(word)):
        matches = True
        for feature, value in left.items():
          if value == 'α':
            if lu[feature] != ru[feature]:
              matches = False
          elif lu[feature] != value:
            matches = False

        for feature, value in right.items():
          if value == 'α':
            if ru[feature] != lu[feature]:
              matches = False
          elif ru[feature] != value:
            matches = False

        for feature, value in target.items():
          if tu[feature] != value:
            matches = False

        if matches:
          new_word[j + 1] = (change.apply(tu, {'left': lu, 'right': ru}), ts)
      data[i] = new_word

  return rules
