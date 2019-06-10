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

def convert_ipa(ipa_string,dictionary):
    nipa_string = []
    ipa_string = ipa_string.replace('kʻ','1')
    ipa_string = ipa_string.replace('pʰ','2')
    ipa_string = ipa_string.replace('tʰ','3')
    for ipa in ipa_string:
        if ipa in dictionary.keys():
            nipa_string.append(dictionary[ipa])
        else:
            nipa_string.append(ipa)
    return ''.join(map(str, nipa_string))

def convert_str(string,dictionary):
    nstring = []
    string = string.replace('1','kʻ')
    string = string.replace('2','pʰ')
    string = string.replace('3','tʰ')

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
    column_costc = 0
    column_costd = 0

    constraints = []
    for example in data:
        sufA = z3.String('sufA')
        sufB = z3.String('sufB')
        sufC = z3.String('sufC')
        sufD = z3.String('sufD')
        preA = z3.String('preA')
        preB = z3.String('preB')
        preC = z3.String('preC')
        preD = z3.String('preD')
        stemA = z3.String('stem' + str(count) + 'A')
        stemB = z3.String('stem' + str(count) + 'B')
        varA = z3.String('var' + str(count) + 'A')
        varB = z3.String('var' + str(count) + 'B')
        varC = z3.String('var' + str(count) + 'C')
        varD = z3.String('var' + str(count) + 'D')
        pvarA = z3.String('pvar' + str(count) + 'A')
        pvarB = z3.String('pvar' + str(count) + 'B')
        pvarC = z3.String('pvar' + str(count) + 'C')
        pvarD = z3.String('pvar' + str(count) + 'D')
        pstemB = z3.String('pstem' + str(count) + 'B')
        scA = z3.Int('sc'+str(count)+'A')
        scB = z3.Int('sc'+str(count)+'B')
        scC = z3.Int('sc'+str(count)+'C')
        scD = z3.Int('sc'+str(count)+'D')
        pcA = z3.Int('pc'+str(count)+'A')
        pcB = z3.Int('pc'+str(count)+'B')
        pcC = z3.Int('pc'+str(count)+'C')
        pcD = z3.Int('pc'+str(count)+'D')
        constraints.append(z3.Length(varA) <= 1)
        constraints.append(z3.Length(varB) <= 1)
        constraints.append(z3.Length(varC) <= 1)
        constraints.append(z3.Length(varD) <= 1)
        constraints.append(z3.Length(pvarA) <= 1)
        constraints.append(z3.Length(pvarB) <= 1)
        constraints.append(z3.Length(pvarC) <= 1)
        constraints.append(z3.Length(pvarD) <= 1)
        constraints.append(z3.StringVal(convert_ipa(example[0],m)) == z3.Concat(preA, pvarA, stemA, varA, sufA))
        constraints.append(z3.StringVal(convert_ipa(example[1],m)) == z3.Concat(preB, pvarB, stemA, varB, sufB))
        constraints.append(z3.StringVal(convert_ipa(example[2],m)) == z3.Concat(preC, pvarC, stemA, varC, sufC))
        constraints.append(z3.StringVal(convert_ipa(example[3],m)) == z3.Concat(preD, pvarD, stemA, varD, sufD))

        constraints.append(z3.Length(stemB) == z3.Length(varA))
        constraints.append(z3.Length(stemB) == z3.Length(varB))
        constraints.append(z3.Length(stemB) == z3.Length(varC))
        constraints.append(z3.Length(stemB) == z3.Length(varD))
        constraints.append(z3.Length(pstemB) == z3.Length(pvarA))
        constraints.append(z3.Length(pstemB) == z3.Length(pvarB))
        constraints.append(z3.Length(pstemB) == z3.Length(pvarC))
        constraints.append(z3.Length(pstemB) == z3.Length(pvarD))
        constraints.append(z3.If(stemB == varA,0,1) == scA)
        constraints.append(z3.If(stemB == varB,0,1) == scB)
        constraints.append(z3.If(stemB == varC,0,1) == scC)
        constraints.append(z3.If(stemB == varD,0,1) == scD)
        constraints.append(z3.If(pstemB == pvarA,0,1) == pcA)
        constraints.append(z3.If(pstemB == pvarB,0,1) == pcB)
        constraints.append(z3.If(pstemB == pvarC,0,1) == pcC)
        constraints.append(z3.If(pstemB == pvarD,0,1) == pcD)
        cost_constraint = cost_constraint + scA + scB + scC + scD + pcA + pcB + pcC + pcD

        count += 1
    return constraints, cost_constraint, column_costa, column_costb, column_costc, column_costd

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
    for i in range(len(data)):
        sA = convert_str(str(model[z3.String('preA')]),m) + convert_str(str(model[z3.String('pvar' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('sufA')]),m)
        sB = convert_str(str(model[z3.String('preB')]),m) + convert_str(str(model[z3.String('pvar' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('sufB')]),m)
        sC = convert_str(str(model[z3.String('preC')]),m) + convert_str(str(model[z3.String('pvar' + str(count) + 'C')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'C')]),m) + convert_str(str(model[z3.String('sufC')]),m)
        sD = convert_str(str(model[z3.String('preD')]),m) + convert_str(str(model[z3.String('pvar' + str(count) + 'D')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('var' + str(count) + 'D')]),m) + convert_str(str(model[z3.String('sufD')]),m)
        urA = convert_str(str(model[z3.String('preA')]),m) + convert_str(str(model[z3.String('pstem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('sufA')]),m)
        urB = convert_str(str(model[z3.String('preB')]),m) + convert_str(str(model[z3.String('pstem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('sufB')]),m)
        urC = convert_str(str(model[z3.String('preC')]),m) + convert_str(str(model[z3.String('pstem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('sufC')]),m)
        urD = convert_str(str(model[z3.String('preD')]),m) + convert_str(str(model[z3.String('pstem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'A')]),m) + convert_str(str(model[z3.String('stem' + str(count) + 'B')]),m) + convert_str(str(model[z3.String('sufD')]),m)
        output_data.append(sA)
        output_data.append(sB)
        output_data.append(sC)
        output_data.append(sD)

        input_data.append(urA)
        input_data.append(urB)
        input_data.append(urC)
        input_data.append(urD)

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

    for i in range(8,20):
        models = add_cost_constraint(constraints,i,cost_constraints)
        rule = print_rule(models)
        if rule:
            break