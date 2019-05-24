from phonosynthesis import sat

class Change:
  def __init__(self, change_vsa):
    self.insertion = change_vsa.insertion
    self.complete_change, self.simplified_change = sat.infer_change(change_vsa)

  def __repr__(self):
    return repr(self.simplified_change)

  def is_contextual(self, feature):
    return self.complete_change[feature] not in {'+', '-', '0'}

  def is_insertion(self):
    return self.insertion

  def apply(self, target, context):
    output = target.copy()
    for feature, value in self.complete_change.items():
      if self.is_contextual(feature):
        output[feature] = context[value][feature]
      else:
        output[feature] = value
    return output


class ChangeVsa:
  def __init__(self, old, new, context):
    self.data = [(old, new, context)]

    insertion = False
    changes = {}
    necessary_features = set()

    if old['deleted'] == '+':
      insertion = True

    for feature, value in new.items():
      if old[feature] != value:
        necessary_features.add(feature)

      values = {value}
      for position, phone in context.items():
        if phone[feature] == value:
          values.add(position)
      changes[feature] = frozenset(values)

    self.insertion = insertion
    self.changes = changes
    self.necessary_features = frozenset(necessary_features)

  def __repr__(self):
    relevant_changes = {}
    for feature in self.necessary_features:
      relevant_changes[feature] = self.changes[feature]
    return repr(relevant_changes)

  def __and__(self, other):
    if self.insertion != other.insertion:
      return None

    necessary_features = self.necessary_features | other.necessary_features
    changes = {}

    for feature in necessary_features:
      if feature not in self.changes or feature not in other.changes:
        return None

    for feature in self.changes.keys() & other.changes.keys():
      value = self.changes[feature] & other.changes[feature]
      if value:
        changes[feature] = value
      elif feature in necessary_features:
        return None

    data = self.data + other.data

    for old, new, context in data:
      for feature, value in new.items():
        if feature in changes:
          for feature, values in changes.items():
            for value in values:
              if value in {'+', '-', '0'}:
                assert(new[feature] == value)
              else:
                real_value = context[value][feature]
                assert (new[feature] == real_value)
        else:
          assert(old[feature] == new[feature])

    change = self.__new__(self.__class__)
    change.insertion = self.insertion
    change.data = data
    change.changes = changes
    change.necessary_features = necessary_features
    return change

  def to_change(self):
    return Change(self)
