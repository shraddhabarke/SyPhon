import time
import sys
import os, os.path
import platform
import pickle
import random
import fileinput
import csv 
from ast import literal_eval
import json

from subprocess import call, check_output, STDOUT

if platform.system() in ['Linux', 'Darwin']:
    TIMEOUT_CMD = 'timeout'                                     # Timeout command
    TIMEOUT = '120'                                             # Timeout value (seconds)    

LOGFILE = 'results.log'                                         # Log file
DUMPFILE = 'results'                                            # Result serialization file
CSV_FILE = 'result.csv'                                         # CSV-output file
LATEX_FILE = 'results.tex'     
FNULL = open(os.devnull, 'w')                                   # Null file

class Benchmark:
    def __init__(self, name, description, time,rule,hold_out):
        self.name = name                # Id (Filename)
        self.description = description  # Description (in the table)
        self.time = time
        self.rule = rule
        self.hold_out = hold_out

    def str(self):
        return self.name + ': ' + self.description 

UF_BENCHMARKS = [
        Benchmark('benchmarks/Dutch','',0.0,[],''),
        Benchmark('benchmarks/German','',0.0,[],''),
        Benchmark('benchmarks/AxinicaCampa','',0.0,[],''),
        Benchmark('benchmarks/Turkish','',0.0,[],''),
        Benchmark('benchmarks/Russian','',0.0,[],''),
        Benchmark('benchmarks/Farsi','',0.0,[],''),
        Benchmark('benchmarks/Korean','',0.0,[],''),
        Benchmark('benchmarks/Polish','',0.0,[],''),
        Benchmark('benchmarks/Hungarian','',0.0,[],''),
        Benchmark('benchmarks/Kerewe','',0.0,[],''),
]

ALT_BENCHMARKS = [
        Benchmark('benchmarks/Farsi','',0.0,[],''),
        Benchmark('benchmarks/Ganda','',0.0,[],''),
        Benchmark('benchmarks/Palauan','',0.0,[],''),
        Benchmark('benchmarks/Proto-Bantu','',0.0,[],''),
        Benchmark('benchmarks/Kishambaa','',0.0,[],''),
        Benchmark('benchmarks/Mohawk','',0.0,[],''),
        Benchmark('benchmarks/Osage','',0.0,[],''),
        Benchmark('benchmarks/Gen','',0.0,[],''),
        Benchmark('benchmarks/Papago','',0.0,[],''),
        Benchmark('benchmarks/Kikurai','',0.0,[],'')
]

SUP_BENCHMARKS = [
        Benchmark('benchmarks/Scottish','',0.0,[],''),
        Benchmark('benchmarks/Lithuanian','',0.0,[],''),
        Benchmark('benchmarks/English','',0.0,[],''),
        Benchmark('benchmarks/Kikuyu','',0.0,[],''),
        Benchmark('benchmarks/Armenian','',0.0,[],'')
]

def hold_out(rf,wf):
    with open(rf, "rb") as source:
        lines = [line for line in source]
        count = len(lines)
    score = int(round(0.2*count))
    random_choice = random.sample(lines, score)
    nrandomchoice = [str(elem,'utf-8') for elem in random_choice]
    with open(wf, "w+") as sink:
        for s in nrandomchoice:
            if "\n" in s:
                sink.write("%s" % s)
            else:
                sink.write("%s\n" % s)

def convert_to_dict(rfname):
    with open(rfname) as f:
        reader = csv.reader(f, skipinitialspace=True)
        result = dict(reader)
    return result

def get_key(dictionary,s):
    for key, value in dictionary.items():
        if s == value:
            return key
    
def generate_input(rfname,input_dict):
    input, output = [], []
    with open(rfname) as rf:
        reader = csv.reader(rf)
        for row in reader:
            keyA = get_key(input_dict,row[0])
            keyB = get_key(input_dict,row[1])
            output.append(row[0])
            output.append(row[1])
            input.append(keyA)
            input.append(keyB)
    return input, output

def compute_diff(input,output):
    if is_diff(input,output):
        change = [i for i in range(len(input)) if input[i] != output[i]]
        leftcon,rightcon = '', ''
        if change[0] == 1:
            leftcon = '#'
        else:
            leftcon = input[change[0]-1]
        if change[0] == (len(input)- 1):
            rightcon = '#'
        else: 
            rightcon = input[change[0]+1]
        return output[change[0]], input[change[0]], leftcon, rightcon
    else:
        return False

def is_diff(input,output):
    change = [i for i in range(len(input)) if input[i] != output[i]]
    if not change:
        return False
    else:
        return True

def is_equal(test_rule,oracle):
    with open('riggle.csv') as csvfile:
        reader = csv.DictReader(csvfile)
        for row in reader:
            if row['symbol'] == test_rule:
                if all(oracle[change] == row[change] for change in oracle):
                    print("Works!")
                    return True
            elif test_rule == '':
                if not oracle:
                    return True
    return False    

def check_rule(rules,data_point):
    for rule in rules:
        change_inf = rule[0]
        condition_inf = rule[1][1]
        leftcon_inf = rule[1][0]
        rightcon_inf = rule[1][2]
        print(data_point[0],change_inf)
        print(data_point[1],condition_inf)
        print(data_point[2],leftcon_inf)
        print(data_point[3],rightcon_inf)
        change = is_equal(data_point[0],change_inf)
        condition = is_equal(data_point[1],condition_inf)
        leftcon = is_equal(data_point[2],leftcon_inf)
        rightcon = is_equal(data_point[3],rightcon_inf)
        if change and condition and leftcon and rightcon:
            continue
        else:
            return False
    return True

def run_benchmark(name,filename):
    with open('SYPHON_LOG', 'w+') as syphon_log:
        start = time.time()
        # Run Spyder on the benchmark:
        call(['python',filename, name + '-UF.csv'], stdout=syphon_log, stderr=syphon_log)
        end = time.time()   
        print(["{0:0.2f}".format(end - start)])
        return format(["{0:0.2f}".format(end - start)])

def write_csv():
    '''Generate CSV file from the results dictionary'''
    with open(CSV_FILE, 'w') as outfile:
        for b in ufbenchmarks:
                outfile.write (b.name + ',')
                outfile.write (format(b.time) + ',')
                outfile.write (str(b.rule) + ',')
                outfile.write (b.hold_out)
                outfile.write ('\n')
    print(outfile)

if __name__ == '__main__':
    ufbenchmarks = UF_BENCHMARKS
    for b in ufbenchmarks:
        check_list = []
        b.time = run_benchmark(b.name,'underlying.py')
        rule = open('SYPHON_LOG', "r").readlines()[-1]
        print(rule)
        b.rule = literal_eval(rule)
        hold_out(b.name+'-UF.csv',b.name+'-H.csv')
        input_dict = convert_to_dict(b.name + '.csv')
        input = generate_input(b.name+'-H.csv',input_dict)[0]
        output = generate_input(b.name+'-H.csv',input_dict)[1]
        test_set = list(zip(input,output))
        print(test_set)
        for test in test_set:
            diff = compute_diff(test[0],test[1])
            if diff:
                print(diff)
                test_pass = check_rule(b.rule, diff)
                check_list.append(test_pass)
        if all(test_cases == True for test_cases in check_list):
            b.hold_out = 'Pass'
    write_csv()


