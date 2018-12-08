#! /usr/bin/env python3

import csv, sys
from functools import reduce

def read_phone(filename):
  '''Returns a dictionary with key : feature name and value: list of feature values for all sounds.'''
  with open(filename, 'r') as infile:
    reader = csv.DictReader(infile)
    data = {}
    for row in reader:
      for header, value in row.items():
        try:
          data[header].append(value)
        except KeyError:
          data[header] = [value]
  return data

def read_phones(filename):
  '''Returns a list of OrderedDict for each symbol and it's features.'''
  with open(filename, "r") as f:
    reader = csv.DictReader(f)
    return list(reader)

def intersect(phone_1, phone_2):
  return dict(phone_1.items() & phone_2.items())

def remove_indices(lindex, ltarget):
  '''Removes the elements of ltarget at indices present in lindex.'''
  for index in sorted(lindex, reverse=True):
      ltarget.pop(index)

def add_indices(lindex, ltarget):
  '''Adds the elements of ltarget at indices present in lindex'''
  ntarget = []
  for index in sorted(lindex, reverse=True):
    ntarget.append(ltarget[index])
  return ntarget

def remove_pos(data, dictname):
  target_indices = ([i for i, x in enumerate(data["target"]) if x == "1"])
  for key, value in dictname.items():
    remove_indices(target_indices, data[key])

def check_negative(filename, dictname):
  '''Removes those features from dictname that are not consistent with negative examples'''
  data = read_phone(filename)
  posexamples = ([i for i, x in enumerate(data["target"]) if x == "1"])
  remove_pos(data, dictname)
  ndict = dictname.copy()
  for key,value in dictname.items():
    if any(value == x for x in data[key]):
      ndict.pop(key,None)
  return ndict

def weakest_classifier(filename):
  phones = read_phones(filename)
  selected_phones = filter(lambda phone: phone["target"] == "1", phones)
  classifier = reduce(intersect, selected_phones)
  nclassifier = check_negative(filename,classifier)
  nclassifier.pop("target",None)
  return nclassifier

def strongest_sound_classifier(filename):
  phones = read_phones(filename)
  selected_phones = filter(lambda phone: phone["target"] == "1", phones)
  classifier = reduce(intersect, selected_phones)
  nclassifier = {k : v for (k, v) in classifier.items() if not k.startswith('L') and not k.startswith('R') and k != "target" and v != "0"}
  return nclassifier

def strongest_context_classifier(filename):
  phones = read_phones(filename)
  selected_phones = filter(lambda phone: phone["target"] == "1", phones)
  classifier = reduce(intersect, selected_phones)
  nclassifier = {k : v for (k, v) in classifier.items() if k.startswith('L') and v != "0" or k.startswith('R') and k != "target" and v != "0"}
  return nclassifier

def get_sat_formulas(filename, featuredict):
  phones = read_phones(filename)
  selected_features = featuredict.keys()
  for elem in phones:
    sat_list = []
    sat_list.append("(assert ")
    for (feature,value) in elem.items():
      if feature == "target" and elem[feature] == "1":
        sat_list.append("(and ")
      elif feature == "target" and elem[feature] == "0":
        sat_list.append("(not (and ")
    for (feature,value) in elem.items():
      if feature in selected_features:
        x = "("+"=> "+feature+"i "+feature+"p"+")" if value == "+" else "("+"=> "+feature+"i "+"("+"not "+ feature + "p"+")"+")"
        sat_list.append(x)
    for (feature,value) in elem.items():
      if feature == "target" and elem[feature] == "1":
        sat_list.append("))")
      elif feature == "target" and elem[feature] == "0":
        sat_list.append(")))")
    print(''.join(map(str, sat_list)))

def get_moresat_formulas(filename, featuredict):
  phones = read_phones(filename)
  selected_features = featuredict.keys()
  for elem in phones:
    sat_list = []
    sat_list.append("(assert ")
    for (feature,value) in elem.items():
      if feature == "target" and elem[feature] == "1":
        sat_list.append("(and ")
      elif feature == "target" and elem[feature] == "0":
        sat_list.append("(not (and ")
    for (feature,value) in elem.items():
      if feature in selected_features:
        x = "(" + "=>" + " (and " + feature+ "i" + " false) false)" if value == "0" else "(" + "=>" + " (and " + feature+ "i" + " true) true)" if value == featuredict[feature] else "(" + "=>" + " (and " + feature+ "i" + " true) false)"
        sat_list.append(x)
    for (feature,value) in elem.items():
      if feature == "target" and elem[feature] == "1":
        sat_list.append("))")
      elif feature == "target" and elem[feature] == "0":
        sat_list.append(")))")
    print(''.join(map(str, sat_list)))
