#!/usr/bin/env python3

import csv, z3, sys, argparse
from phonosynthesis import phonosynth
from phonosynthesis import ipa_data
data = []
alt_forms = []

def create_arg_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument('inputDirectory',
                    help='Path to the input directory.')
    parser.add_argument('--outputDirectory',
                    help='Path to the output that contains the results.')
    return parser

arg_parser = create_arg_parser()
parsed_args = arg_parser.parse_args(sys.argv[1:])
fname = parsed_args.inputDirectory

with open(fname) as rf:
    reader = csv.reader(rf)
    for row in reader:
        if row[0] != "U":
            print(row)
            data.append(''.join(row))
        elif row[0] == "U":
            print(row)
            alt_forms.append((row[1],row[2]))
            print(alt_forms)

def generate_alternating_form(data,source,fst,snd):
    possible_config = []
    for example in data:
        nexample = [example.replace(source[i][fst],source[i][snd]) for i in range(len(source)) if source[i][fst] in example]
        if len(nexample) == 0:
            possible_config.append(example)
        if len(nexample) == 1:
            possible_config.append(nexample[0])
        elif len(nexample) >= 2:
            possible_config.append(nexample[-1])
    return possible_config

configA = generate_alternating_form(data,alt_forms,0,1)
print(configA)
configB = generate_alternating_form(data,alt_forms,1,0)
print(configB)
wordsA = zip(configA,data)
wordsB = zip(configB,data)

def get_rules(words):
    data = phonosynth.parse(words)
    changes = phonosynth.infer_change(data)
    rules = phonosynth.infer_rule(data, changes)
    return rules

def num_rules(rules):
    return(len(rules))

def num_features(rule):
    num_condition = 0
    num_change = len(rule[0].keys())
    for dictionary in rule[1]:
        count = len(dictionary.keys()) 
        num_condition += count
    total_features = num_change + num_condition
    return(total_features)

def select_rule(r1,r2):
    if r1[0] == None:
        return r2
    elif r2[0] == None:
        return r1
    rA = num_rules(r1)
    rB = num_rules(r2)
    print(rA,rB)
    if rA > rB:
        return r2
    elif rA < rB:
        return r1
    elif rA == 1 and rB == 1:
        if num_features(r1[0]) > num_features(r2[0]):
            return r2[0]
        elif num_features(r1[0]) < num_features(r2[0]):
            return r1[0]
    else:
        fA = 0
        fB = 0
        for r in r1:
            fA += num_features(r)
        for r in r2:
            fB += num_features(r)
        if fA > fB:
            return r2
        elif fB > fA:
            return r1


if __name__ == "__main__":
    rules1 = get_rules(wordsA)
    rules2 = get_rules(wordsB)
    print(select_rule(rules1,rules2))
 



