#!/usr/bin/env python3

import csv, sys, itertools
from functools import reduce
import implied

def read_words(filename):
  with open(filename, "r") as f:
    reader = csv.DictReader(f, fieldnames=["word", "realization"])
    return list(reader)

def read_phones(filename):
  with open(filename, "r") as f:
    reader = csv.DictReader(f)
    phones = []
    for phone in reader:
      phone["word boundary"] = "-"
      phones.append(phone)
    return phones

def to_triples(l):
  left, middle = itertools.tee(l)
  next(middle)
  middle, right = itertools.tee(middle)
  next(right)
  return zip(left, middle, right)

def word_to_phones(word, phones_by_symbol):
  return ([phones_by_symbol[ipaize(symbol)] for symbol in word["word"]], [phones_by_symbol[ipaize(symbol)] for symbol in word["realization"]])

def triples_changed(word):
  end = frozenset({("symbol", "#"), ("word boundary", "+")})
  triples = to_triples([end] + word[0] + [end])
  return [(triple, triple[1] != word[1][i]) for i, triple in enumerate(triples)]

def intersect_phones(phone_1, phone_2):
  return dict(phone_1.items() & phone_2.items())

def intersect_triples(triple_1, triple_2):
  return [intersect_phones(phone_1, phone_2) for phone_1, phone_2 in zip(triple_1, triple_2)]

def strongest_triple_classifier(triples):
  return map(remove_zeros, reduce(intersect_triples, triples))

def invert_phone(phone):
  return {key: {'+': '-', '-': '+'}.get(value, value) for key, value in phone.items()}

def weakest_classifier(phone, changed):
  if not changed:
    phone = invert_phone(phone)
  return set(map(frozenset, phone.items()))

def add_triple(classifier, triple, changed):
  if changed:
    triple_classifier = set()
    for i, phone in enumerate(triple):
      triple_classifier |= {(i, feature, value) for feature, value in phone.items()}
    return {conjunction for conjunction in classifier if conjunction <= triple_classifier}
  else:
    new_classifier = set()
    for conjunction in classifier:
      inverted_phone = invert_phone(phone)
      if phone.items() & conjunction != set() and inverted_phone.items() & conjunction == set():
        new_classifier |= {conjunction | {(feature, value)} for feature, value in inverted_phone.items()}
      else:
        new_classifier.add(conjunction)
    return new_classifier

def classify(triples):
  initial_triple, initial_changed = triples.pop(0)
  classifiers = [weakest_classifier(phone, initial_changed) for phone in initial_triple]
  for triple, changed in triples:
    for i, phone in enumerate(triple):
      classifiers[i] = add_phone(classifiers[i], phone, changed)
  return classifiers

def strongest_classifier_triple(triple):
  classifier = set()
  for i, phone in enumerate(triple):
    for feature, value in phone:
      classifier.add((i, feature, value))
  return classifier

def strongest_classifier_triples(triples):
  return reduce(set.intersection, map(strongest_classifier_triple, triples))

def powerset(s):
  return map(frozenset, itertools.chain.from_iterable(itertools.combinations(s, i) for i in range(len(s)+1)))

def matches_any(conj, triples):
  for triple in triples:
    if conj <= strongest_classifier_triple(triple):
      return True
  return False

def strengthen_triples(classifier, triples):
  strengthened_classifier = set()
  for conj in classifier:
    if not matches_any(conj, triples):
      strengthened_classifier.add(conj)
  return strengthened_classifier

def remove_zeros(phone):
  return {feature: value for feature, value in phone.items() if value != "0"}

def ipaize(symbol):
  to_unicode = {"g" : "ɡ"}
  return to_unicode.get(symbol, symbol)

if __name__ == "__main__":
  phones = read_phones(sys.argv[1])
  phones_by_symbol = {phone["symbol"]: frozenset(phone.items()) for phone in phones}
  words = read_words(sys.argv[2])
  phone_words = [word_to_phones(word, phones_by_symbol) for word in words]
  triples = itertools.chain.from_iterable(map(triples_changed, phone_words))
  changed_triples = set()
  unchanged_triples = set()
  for triple, changed in triples:
    if changed:
      changed_triples.add(triple)
    else:
      unchanged_triples.add(triple)
  strongest_classifier = strongest_classifier_triples(changed_triples)
  weakest_classifiers = powerset(strongest_classifier)
  weakest_classifiers = strengthen_triples(weakest_classifiers, unchanged_triples)
  print(weakest_classifiers)
  #print(list(map(implied.minimize, strongest_classifier)))
