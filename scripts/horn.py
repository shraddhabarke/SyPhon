#!/usr/bin/env python3

import csv, sys, itertools, re
from functools import reduce
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

def gen_conjunction(triple):
  def gen_conjunction_features(features):
    feature, location, value = features.pop(0)
    feature_ident = to_identifier(feature, location)
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
        features.append((feature, locations[i], value == "+"))

  return gen_conjunction_features(features)

def gen_horn_clause(feature_idents, triple, changed):
  decls = gen_decls(feature_idents)
  conjunction = gen_conjunction(triple)
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
    print(gen_horn_clause(feature_idents, triple, changed))

if __name__ == "__main__":
  phones = learn_triples.read_phones(sys.argv[1])
  feature_idents = to_identifiers(phones[0].keys())
  phones_by_symbol = {phone["symbol"]: frozenset(phone.items()) for phone in phones}
  words = learn_triples.read_words(sys.argv[2])
  phone_words = [learn_triples.word_to_phones(word, phones_by_symbol) for word in words]
  triples = itertools.chain.from_iterable(map(learn_triples.triples_changed, phone_words))
  print_msmt(feature_idents, triples)
