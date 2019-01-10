import csv, sys, itertools

def get_implications(phones, features):
  def implies(feature1, value1, feature2, value2):
    for phone in phones:
      if feature1 in phone and feature2 in phone:
        if phone[feature1] == value1 and phone[feature2] != value2:
          return False
    return True
  implications = {}
  reverse_implications = {}
  for feature1 in features:
    for feature2 in features:
      if feature1 != feature2:
        for value1 in ['+', '-']:
          for value2 in ['+', '-']:
            if implies(feature1, value1, feature2, value2):
              if (feature1, value1) not in implications:
                implications[(feature1, value1)] = [(feature2, value2)]
              else:
                implications[(feature1, value1)].append((feature2, value2))
              if (feature2, value2) not in reverse_implications:
                reverse_implications[(feature2, value2)] = [(feature1, value1)]
              else:
                reverse_implications[(feature2, value2)].append((feature1, value1))
  return (implications, reverse_implications)
