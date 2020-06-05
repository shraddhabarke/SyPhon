import csv, z3, sys, argparse
from phonosynthesis import phonosynth, ipa_data

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

m = {'ø':'A', 'ʃ':'B', 'ɯ':'C', 'ʤ':'D', 'ʧ': 'E', 'ː':'F', 'ɛ':'G', 'ə':'H', 'ɑ': 'I', 'œ':'J', 'ŋ': 'K', 'ʋ':'L', 'ʌ':'M', 'ʊ':'N', 'ʦ':'P', 'æ':'Q', 'ʣ':'R', 'ʈ':'S', 'ɖ':'T', 'ʒ':'U', 'ɱ':'V', 'ɩ':'W', 'ɲ': 'Y'}
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
    print(ipa_string," > ",nipa_string,dictionary)
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


def generate_constraints(data):
    I = len(data[0]) # number of inflections
    
    count = 0
    cost_constraint = 0
    column_cost = [0]*I
    length_c = 0
    constraints = []
    for example in data:
        suffixes = [z3.String('suf' + chr(ord('A') + i))
                    for i in range(I) ]
        prefixes = [z3.String('pre' + chr(ord('A') + i))
                    for i in range(I) ]
        # preA = z3.String('preA')
        # preB = z3.String('preB')
        # sufA = z3.String('sufA')
        # sufB = z3.String('sufB')
        stem = z3.String('stem' + str(count))

        # 1 is associated with the prefix
        unch1 = [z3.String('unch1' + str(count) + chr(ord('A') + i))
                 for i in range(I) ]
        # 2 is associated with the suffix
        unch2 = [z3.String('unch2' + str(count) + chr(ord('A') + i))
                 for i in range(I) ]

        # unchA1 = z3.String('unch' + str(count) + 'A') 
        # unchA2 = z3.String('unch' + str(count) + 'B')

        # unchB1 = z3.String('unch' + str(count) + 'C')
        # unchB2 = z3.String('unch' + str(count) + 'D')

        ch = [z3.String('ch' + str(count) + chr(ord('A') + i))
              for i in range(I) ]

        var = [z3.String('var' + str(count) + chr(ord('A') + i))
              for i in range(I) ]
        # varA = z3.String('var' + str(count) + 'A')
        # varB = z3.String('var' + str(count) + 'B')

        # scA = z3.Int('sc'+str(count)+'A')
        # scB = z3.Int('sc'+str(count)+'B')
        sc = [z3.Int('sc' + str(count) + chr(ord('A') + i))
              for i in range(I) ]
        
        lc = z3.Int('l'+str(count))
        for v in var:
            constraints.append(z3.Length(v) <= 1)
        # constraints.append(z3.Length(varA) <= 1)
        # constraints.append(z3.Length(varB) <= 1)
        for i in range(I):
            constraints.append(z3.Concat(prefixes[i],stem,suffixes[i]) == z3.Concat(unch1[i],ch[i],unch2[i]))
        # constraints.append(z3.Concat(preA,stem,sufA) == z3.Concat(unchA1,chA,unchA2))
        # constraints.append(z3.Concat(preB,stem,sufB) == z3.Concat(unchB1,chB,unchB2))
        for i in range(I):
            if len(example[i]) == 0: continue
            constraints.append(z3.StringVal(convert_ipa(example[i],m)) == z3.Concat(unch1[i],var[i],unch2[i]))
            
        # constraints.append(z3.StringVal(convert_ipa(example[0],m)) == z3.Concat(unchA1,varA,unchA2))
        # constraints.append(z3.StringVal(convert_ipa(example[1],m)) == z3.Concat(unchB1,varB,unchB2))
        
        constraints.append(z3.Length(stem) == lc)

        for i in range(I):
            constraints.append(z3.If(ch[i] == var[i],0,1) == sc[i])
            
        #constraints.append(z3.If(chB == varB,0,1) == scB)
        
        length_c = length_c + lc

        for i in range(I):
            constraints.append(sc[i] <= 1)
        cost_constraint = cost_constraint + sum(sc)
        for i in range(I):
            column_cost[i] = column_cost[i] + sc[i]
        count += 1
    return constraints, cost_constraint, column_cost

def get_models(constraint_formula):
    model = []
    s = z3.Solver()
    s.add(constraint_formula)
    print(s.sexpr())
    if s.check() == z3.sat:
        m = s.model()
        model.append(m)
    return model

def add_cost_constraint(constraints,cost_bound,cost_constraint,column_cost):
    constraints.append(cost_constraint == cost_bound)
    if column_cost is not None:
        constraints.append(column_cost == 0) 
    models = get_models(constraints)
    constraints.remove(cost_constraint == cost_bound)
    if column_cost is not None:
        constraints.remove(column_cost == 0)
    return models

def get_rules(words):
    data = phonosynth.parse(words)
    changes = phonosynth.infer_change(data)
    rules = phonosynth.infer_rule(data, changes)
    return rules

def insert_or_delete(u,s,letter):
    nu = []
    nus = ""
    changed_index = [i for i in range(len(u)) if s[i] != u[i]]
    if len(changed_index) == 0:
        nu = u + letter
    else:
        i = 0
        while (i != changed_index[0] and i < len(u)):
            nu += u[i]
            i = i + 1
        nu += letter
        for i in range(changed_index[0],len(u)):
            nu += u[i]
    nu = list(filter(lambda i: i != '"', nu))
    n = nus.join(nu)
    return n 

def create_word(data,model):
    input_data = []
    output_data = []
    I = len(data[0])
    for count in range(len(data)):
        surface = [convert_str(str(model[z3.String('unch1' + str(count) + chr(ord('A') + i))]),m) + \
                   convert_str(str(model[z3.String('var' + str(count) + chr(ord('A') + i))]),m) + \
                   convert_str(str(model[z3.String('unch2' + str(count) + chr(ord('A') + i))]),m)
                   for i in range(I) ]
        underlying = [convert_str(str(model[z3.String('unch1' + str(count) + chr(ord('A') + i))]),m) + \
                      convert_str(str(model[z3.String('ch' + str(count) + chr(ord('A') + i))]),m) + \
                      convert_str(str(model[z3.String('unch2' + str(count) + chr(ord('A') + i))]),m)
                      for i in range(I) ]
        
        nur = [""]*I
        ns = [""]*I
        for i in range(I):
            if len(surface[i]) < len(underlying[i]) and not(any(elem in diacritics for elem in surface[i])) and not(any(elem in diacritics for elem in underlying[i])):
                ns[i] = insert_or_delete(surface[i],underlying[i],'∅')

        for i in range(I):
            if len(surface[i]) > len(underlying[i]) and not(any(elem in diacritics for elem in surface[i])) and not(any(elem in diacritics for elem in underlying[i])):
                nur[i] = insert_or_delete(underlying[i],surface[i],'∅')

        for i in range(I):
            if ns[i] != "":
                output_data.append(ns[i])
            else:
                output_data.append(surface[i])

        for i in range(I):
            if nur[i] != "":
                input_data.append(nur[i])
            else:
                input_data.append(underlying[i])

    words = list(zip(list(map(lambda x: x.replace('"',""), input_data)),list(map(lambda x: x.replace('"',""), output_data))))
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
    column_cost = z3_constraints[2]
    #length = round(len(data)/3)
    assert len(column_cost) == len(data[0])
    for i in range(4,20,2):
        # for some reason, we only add the column cost constraint when there are 2 inflections
        if len(data[0]) <= 2: ccs = [ele for ele in reversed(column_cost)]
        else: ccs = [None]
        for cc in ccs:
            model = add_cost_constraint(constraints,i,cost_constraints,cc)
            
            rule = print_rule(model)
            print(rule)
            if rule:
                #print("Successful synthesis!")
                sys.exit(0)