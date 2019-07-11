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

m = {'ø':'A', 'ʃ':'B', 'ɯ':'C', 'ʤ':'D', 'ʧ': 'E', 'ː':'F', 'ɛ':'G', 'ə':'H', 'ɑ': 'I', 'œ':'J', 'ŋ': 'K', 'ʋ':'L', 'ʌ':'M', 'ʊ':'N', 'ʦ':'P', 'æ':'Q', 'ʣ':'R', 'ʈ':'S', 'ɖ':'T', 'ʒ':'U', 'ɱ':'V', 'ɩ':'W'}
diacritics = ['ʻ','ʰ','ʲ']

def convert_ipa(ipa_string,dictionary):
    nipa_string = []
    # ipa_string = ipa_string.replace('kʻ','1')
    # ipa_string = ipa_string.replace('pʰ','2')
    # ipa_string = ipa_string.replace('tʰ','3')
    
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
    # string = string.replace('1','kʻ')
    # string = string.replace('2','pʰ')
    # string = string.replace('3','tʰ')

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
print(data)

def generate_constraints(data):
    count = 0
    cost_constraint = 0
    column_costa = 0
    column_costb = 0
    length_c = 0
    constraints = []
    for example in data:
        preA = z3.String('preA')
        preB = z3.String('preB')
        sufA = z3.String('sufA')
        sufB = z3.String('sufB')
        stem = z3.String('stem' + str(count))
        
        unchA1 = z3.String('unch' + str(count) + 'A') 
        unchA2 = z3.String('unch' + str(count) + 'B')

        unchB1 = z3.String('unch' + str(count) + 'C')
        unchB2 = z3.String('unch' + str(count) + 'D')

        chA = z3.String('ch' + str(count) + 'A')
        chB = z3.String('ch' + str(count) + 'B')

        varA = z3.String('var' + str(count) + 'A')
        varB = z3.String('var' + str(count) + 'B')

        scA = z3.Int('sc'+str(count)+'A')
        scB = z3.Int('sc'+str(count)+'B')
        lc = z3.Int('l'+str(count))
        constraints.append(z3.Length(varA) <= 1)
        constraints.append(z3.Length(varB) <= 1)
        constraints.append(z3.Concat(preA,stem,sufA) == z3.Concat(unchA1,chA,unchA2))
        constraints.append(z3.Concat(preB,stem,sufB) == z3.Concat(unchB1,chB,unchB2))
        constraints.append(z3.StringVal(convert_ipa(example[0],m)) == z3.Concat(unchA1,varA,unchA2))
        constraints.append(z3.StringVal(convert_ipa(example[1],m)) == z3.Concat(unchB1,varB,unchB2))
        constraints.append(z3.Length(stem) == lc)
        constraints.append(z3.If(chA == varA,0,1) == scA)
        constraints.append(z3.If(chB == varB,0,1) == scB)
        length_c = length_c + lc
        constraints.append(scA <= 1)
        constraints.append(scB <= 1)
        cost_constraint = cost_constraint + scA + scB 
        column_costa = column_costa + scA
        column_costb = column_costb + scB 
        count += 1
    return constraints, cost_constraint, column_costa, column_costb

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
    constraints.append(column_cost == 0) 
    models = get_models(constraints)
    constraints.remove(cost_constraint == cost_bound)
    constraints.remove(column_cost == 0)
    return models

def get_rules(words):
    data = phonosynth.parse(words)
    changes = phonosynth.infer_change(data)
    rules = phonosynth.infer_rule(data, changes)
    return rules

def insert_or_delete(u,s,letter):
    nu = ""
    changed_index = [i for i in range(len(u)) if s[i] != u[i]]
    if len(changed_index) == 0:
        nu = u + letter
    else:
        i = 0
        while (i != changed_index[0] and i < len(u)):
            nu += u[i]
            print(nu)
            i = i + 1
        nu += letter
        print(nu)
        for i in range(changed_index[0],len(u)):
            nu += u[i]
            print(nu)
    return nu

def create_word(data,model):
    count = 0
    input_data = []
    output_data = []
    for i in range(len(data)):
        sA = convert_str(str(model[z3.String('unch' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('unch' + str(count) + 'B')]),m) 
        sB =  convert_str(str(model[z3.String('unch' + str(count) + 'C')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('unch' + str(count) + 'D')]),m)
        urA = convert_str(str(model[z3.String('unch' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('ch' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('unch' + str(count) + 'B')]),m)
        urB = convert_str(str(model[z3.String('unch' + str(count) + 'C')]),m) + convert_str(str(model[z3.String('ch' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('unch' + str(count) + 'D')]),m) 
        nurA = ""
        nurB = ""
        nsA = ""
        nsB = ""
        if len(sA) < len(urA) and not(any(elem in diacritics for elem in sA)) and not(any(elem in diacritics for elem in urA)):
            nsA = insert_or_delete(sA,urA,'∅')
        if len(sB) < len(urB) and not(any(elem in diacritics for elem in sB)) and not(any(elem in diacritics for elem in urB)):
            nsB = insert_or_delete(sB,urB,'∅')
        if len(sA) > len(urA) and not(any(elem in diacritics for elem in sA)) and not(any(elem in diacritics for elem in urA)):
            nurA = insert_or_delete(urA,sA,'∅')
        if len(sB) > len(urB) and not(any(elem in diacritics for elem in sB)) and not(any(elem in diacritics for elem in urB)):
            nurB = insert_or_delete(urB,sB,'∅')

        if nsA != "":
            output_data.append(nsA)
        else:
            output_data.append(sA)

        if nsB != "":
            output_data.append(nsB)
        else:
            output_data.append(sB)

        if nurA != "":
            input_data.append(nurA)
        else:
            input_data.append(urA)

        if nurB != "":
            input_data.append(nurB)
        else:
            input_data.append(urB)
        count += 1
    words = list(zip(input_data,output_data))
    return words

def print_rule(models):
    for model in models:
            words = create_word(data,model)
            print("WORDS",words)
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
    columna_cost = z3_constraints[2]
    columnb_cost = z3_constraints[3]
    for i in range(4,20):
        print("I = ",i)
        modelB = add_cost_constraint(constraints,i,cost_constraints,columnb_cost)
        print("model",modelB)
        ruleB = print_rule(modelB)
        print(ruleB)
        if ruleB:
            break
        modelA = add_cost_constraint(constraints,i,cost_constraints,columna_cost)
        ruleA = print_rule(modelA)
        print(ruleA)
        if ruleA:
            break
