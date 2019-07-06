import csv, z3, sys, argparse
import phonosynth, ipa_data

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

data=[]

m = {'ʧ':'D','ø':'A', 'ʃ':'B', 'ɯ':'C', 'ʤ':'E', 'ː':'F', 'ɛ':'G', 'ə':'H', 'œ':'J', 'ŋ': 'K', 'ʋ':'L', 'ʌ':'M', 'ɑ': 'I', 'ʒ': 'N', 'ʦ':'R', 'ü':'P', 'ɲ':'Q', 'ʣ':'S'}
diacritics = ['ʻ','ʰ','ʲ']

def convert_ipa(ipa_string,dictionary):
    nipa_string = []
    for ipa in ipa_string:
        if ipa in diacritics:
            new_key = get_key(dictionary, nipa_string[-1]) + ipa
            if new_key in dictionary:
                nipa_string[-1] = dictionary[new_key]
            else:
                dictionary[new_key] = get_unused_symbol(dictionary)
                nipa_string[-1] = dictionary[new_key]
        elif ipa in dictionary.keys():
            nipa_string.append(dictionary[ipa])
        else:
            nipa_string.append(ipa)
    return ''.join(map(str, nipa_string))

def get_unused_symbol(d):
    possibilities = [chr(n) for n in range(ord('A'),ord('Z')+1)] + [int(n) for n in range(1,10) ]
    for p in possibilities:
        if p not in d.values(): return p
    assert False, "dictionary could not be made bigger"

def convert_str(string,dictionary):
    nstring = []

    for s in string:
        key = get_key(dictionary,s)
        nstring.append(key)
    return ''.join(nstring)

def get_key(dictionary,s):
    for key, value in dictionary.items():
        if s == value:
            return key
    return s

with open(fname) as rf:
    reader = csv.reader(rf)
    for row in reader:
        data.append(row)
print("Data from CSV:",data)

def generate_constraints(data):
    inflections = len(data[0])
    count = 0
    cost_constraint = 0
    cc = [0]*inflections

    constraints = []
    for example in data:
        suffixes = [z3.String('suf' + chr(ord('A') + i))
                    for i in range(inflections) ]
        prefixes = [z3.String('pre' + chr(ord('A') + i))
                    for i in range(inflections) ]

        stemA = z3.String('stem' + str(count) + 'A')
        stemB = z3.String('stem' + str(count) + 'B')

        variables = [z3.String('var' + str(count) + chr(ord('A') + i))
                    for i in range(inflections) ]

        pvariables = [z3.String('pvar' + str(count) + chr(ord('A') + i))
                     for i in range(inflections) ]
        
        pstemB = z3.String('pstem' + str(count) + 'B')

        sc = [z3.Int('sc' + str(count) + chr(ord('A') + i))
              for i in range(inflections) ]

        pc = [z3.Int('pc' + str(count) + chr(ord('A') + i))
              for i in range(inflections) ]

        for v in variables:
            constraints.append(z3.Length(v) <= 1)
        for v in pvariables:
            constraints.append(z3.Length(v) <= 1)
        for i in range(inflections):
            if len(example[i]) > 0:
                constraints.append(z3.StringVal(convert_ipa(example[i],m)) == z3.Concat(prefixes[i], pvariables[i], stemA, variables[i], suffixes[i]))
            
        for v in variables:
            constraints.append(z3.Length(stemB) == z3.Length(v))

        for v in pvariables:
            constraints.append(z3.Length(pstemB) == z3.Length(v))

        for i in range(inflections):
            constraints.append(z3.If(stemB == variables[i],0,1) == sc[i])

        for i in range(inflections):
            constraints.append(z3.If(pstemB == pvariables[i],0,1) == pc[i])

        for cost_variable in sc + pc:
            cost_constraint = cost_constraint + cost_variable

        count += 1
    return constraints, cost_constraint

def get_models(constraint_formula):
    model = []
    s = z3.Solver()
    s.add(constraint_formula)
    print(s.sexpr())
    if s.check() == z3.sat:
        m = s.model()
        model.append(m)
    return model 

def add_cost_constraint(constraints,cost_bound,cost_constraint):
    constraints.append(cost_constraint == cost_bound) 
    models = get_models(constraints)
    constraints.remove(cost_constraint == cost_bound)
    return models

def get_rules(words):
    data = phonosynth.parse(words)
    changes = phonosynth.infer_change(data)
    rules = phonosynth.infer_rule(data, changes)
    return rules

def create_word(data,model):
    count = 0
    input_data = []
    output_data = []
    numberOfInflections = len(data[0])
    for i in range(len(data)):
        for inflectionIndex,observation in enumerate(data[i]):
            if len(observation) == 0: continue

            inflectionCode = chr(ord('A') + inflectionIndex)
            surface = convert_str(str(model[z3.String('pre' + inflectionCode)]),m) + \
                      convert_str(str(model[z3.String('pvar' + str(count) + inflectionCode)]),m) + \
                      convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + \
                      convert_str(str(model[z3.String('var' + str(count) + inflectionCode)]),m) + \
                      convert_str(str(model[z3.String('suf' + inflectionCode)]),m)
            underlying = convert_str(str(model[z3.String('pre' + inflectionCode)]),m) + \
                         convert_str(str(model[z3.String('pstem' + str(count) + 'B')]),m) + \
                         convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + \
                         convert_str(str(model[z3.String('stem' + str(count) + 'B')]),m) + \
                         convert_str(str(model[z3.String('suf' + inflectionCode)]),m)
            output_data.append(surface)
            input_data.append(underlying)
        

        count += 1
    words = list(zip(input_data,output_data))
    return words

def print_rule(models):
    for model in models:
            words = create_word(data,model)
            print(words)
            rules = get_rules(words)   
            if(None in rules):
                continue
            else:
                print(rules)
                return rules

if __name__ == "__main__":
    z3_constraints = generate_constraints(data)
    constraints = z3_constraints[0]
    cost_constraints = z3_constraints[1]

    for i in range(6,20):
        models = add_cost_constraint(constraints,i,cost_constraints)
        rule = print_rule(models)
        if rule:
            break
        
