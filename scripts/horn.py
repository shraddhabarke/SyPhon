#!/usr/bin/env python3

import csv, sys, itertools, re
from functools import reduce
from pprint import pprint
import learn_triples

def to_identifier(feature, location):
  def escape(name):
    return re.sub(r'(\s|\.)+', '', name.lower())

  return f"{escape(feature)}_{location}"

def to_identifiers(features):
  locations = ['left', 'center', 'right']
  return [to_identifier(feature, location) for feature, location in itertools.product(features, locations)]

def gen_decls(feature_idents):
  return [f"({feature_ident} Bool)" for feature_ident in feature_idents]

def gen_wf(feature_idents):
  decls = gen_decls(feature_idents)
  return f"(wf $formula ({' '.join(decls)}))"

def gen_conjunction(relevant_idents, triple):
  def gen_conjunction_features(features):
    feature_ident, value = features.pop(0)
    literal = feature_ident if value else f"(not {feature_ident})"
    if features != []:
      return f"(and {literal} {gen_conjunction_features(features)})"
    else:
      return literal

  features = []
  locations = ["left", "center", "right"]
  for i, phone in enumerate(triple):
    for feature, value in phone:
      if value in ["+", "-"]:
        feature_ident = to_identifier(feature, locations[i])
        if feature_ident in relevant_idents:
          features.append((feature_ident, value == "+"))

  if features != []:
    return gen_conjunction_features(features)

def gen_horn_clause(feature_idents, triple, changed):
  conjunction = gen_conjunction(feature_idents, triple)
  if conjunction != None:
    decls = gen_decls(feature_idents)
    implication = None
    if changed:
      implication = f"(=> {conjunction} ($formula {' '.join(feature_idents)}))"
    else:
      implication = f"(=> ($formula {' '.join(feature_idents)}) (not {conjunction}))"
    return f"(constraint (forall ({' '.join(decls)}) {implication}))"

def print_msmt(feature_idents, triples):
  print("(qualif Feature ((feature Bool)) feature)")
  print("(qualif NotFeature ((feature Bool)) (not feature))")
  print(gen_wf(feature_idents))
  for triple, changed in triples:
    horn_clause = gen_horn_clause(feature_idents, triple, changed)
    if horn_clause != None:
      print(horn_clause)

if __name__ == "__main__":
  phones = learn_triples.read_phones(sys.argv[1])
  phones_by_symbol = {phone["symbol"]: frozenset(phone.items()) for phone in phones}
  words = learn_triples.read_words(sys.argv[2])
  phone_words = [learn_triples.word_to_phones(word, phones_by_symbol) for word in words]
  triples = list(map(learn_triples.triples_changed, phone_words))
  triples = list(itertools.chain.from_iterable(triples))
  changed_triples = [triple for triple, changed in triples if changed]
  strongest_classifier = learn_triples.strongest_classifier_triples(changed_triples)
  locations = ['left', 'center', 'right']
  relevant_idents = [to_identifier(feature, locations[i]) for i, feature, value in strongest_classifier if value in ["+", "-"]]
  print_msmt(relevant_idents, triples)
