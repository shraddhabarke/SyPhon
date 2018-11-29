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
    return list(reader)

def to_triples(l):
  left, middle = itertools.tee(l)
  next(middle)
  middle, right = itertools.tee(middle)
  next(right)
  return zip(left, middle, right)

def word_to_phones(word, phones_by_symbol):
  return {
    "word": [phones_by_symbol[ipaize(symbol)] for symbol in word["word"]],
    "realization": [phones_by_symbol[ipaize(symbol)] for symbol in word["realization"]]
  }

def triples_changed(word):
  end = {"symbol": "#"}
  triples = to_triples([end] + word["word"] + [end])
  return [(triple, triple[1] != word["realization"][i]) for i, triple in enumerate(triples)]

def intersect_phones(phone_1, phone_2):
  return dict(phone_1.items() & phone_2.items())

def intersect_triples(triple_1, triple_2):
  return [intersect_phones(phone_1, phone_2) for phone_1, phone_2 in zip(triple_1, triple_2)]

def strongest_triple_classifier(triples):
  return map(remove_zeros, reduce(intersect_triples, triples))

def remove_zeros(phone):
  return {feature: value for feature, value in phone.items() if value != "0"}

def ipaize(symbol):
  to_unicode = {"g" : "ɡ"}
  return to_unicode.get(symbol, symbol)

if __name__ == "__main__":
  phones = read_phones(sys.argv[1])
  phones_by_symbol = {phone["symbol"]: phone for phone in phones}
  words = read_words(sys.argv[2])
  phone_words = [word_to_phones(word, phones_by_symbol) for word in words]
  triples = [triple for triple, changed in itertools.chain.from_iterable(map(triples_changed, phone_words)) if changed]
  strongest_classifier = strongest_triple_classifier(triples)
  print(list(map(implied.minimize, strongest_classifier)))
