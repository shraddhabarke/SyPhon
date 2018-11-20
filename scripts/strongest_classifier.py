#! /usr/bin/env python3

import csv, sys
from functools import reduce

def read_phones(filename):
  with open(filename, "r") as f:
    reader = csv.DictReader(f)
    return list(reader)

def intersect(phone_1, phone_2):
  return dict(phone_1.items() & phone_2.items())

def print_phone(phone):
  for (feature, value) in phone.items():
    if value == "+":
      print(feature)
    elif value == "-":
      print("not " + feature)

if __name__ == "__main__":
  filename = sys.argv[1]
  phones = read_phones(filename)
  selected_phones = filter(lambda phone: phone["symbol"] in sys.argv[2:], phones)
  classifier = reduce(intersect, selected_phones)
  print(classifier)
  print_phone(classifier)
