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
        Benchmark('benchmarks/Farsid','',0.0,[],''),
        Benchmark('benchmarks/Korean','',0.0,[],''),
        Benchmark('benchmarks/Polish','',0.0,[],''),
]

UF4_BENCHMARKS = [
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
        Benchmark('benchmarks/Dutch-Roca','',0.0,[],'')
]

TEST_BENCHS = [
        Benchmark('test/CentralAlaskanYupic','',0.0,[],''),
        Benchmark('test/DolakhaNewar','',0.0,[],''),
        Benchmark('test/Ganda','',0.0,[],''),
        Benchmark('test/Greenlandic','',0.0,[],''),
        Benchmark('test/Kongo','',0.0,[],''),
        Benchmark('test/Limbu','',0.0,[],''),
        Benchmark('test/Persian','',0.0,[],''),
        Benchmark('test/Roviana','',0.0,[],''),
        Benchmark('test/SierraPopoluca','',0.0,[],''),
        Benchmark('test/TohonoOodham','',0.0,[],'') ]

def run_ufbenchmark(name,filename):
    with open('SYPHON_LOG', 'w+') as syphon_log:
        start = time.time()
        call(['python',filename, name + '-UF.csv'], stdout=syphon_log, stderr=syphon_log)
        end = time.time()   
        print(["{0:0.2f}".format(end - start)])
        return format(["{0:0.2f}".format(end - start)])

def run_altbenchmark(name,filename):
    with open('SYPHON_LOG', 'w+') as syphon_log:
        start = time.time()
        call(['python',filename, name + '-A.csv'], stdout=syphon_log, stderr=syphon_log)
        end = time.time()   
        print(["{0:0.2f}".format(end - start)])
        return format(["{0:0.2f}".format(end - start)])

def write_csv():
    '''Generate CSV file from the results dictionary'''
    benchmarks = ALT_BENCHMARKS 
    with open(CSV_FILE, 'w') as outfile:
        for b in benchmarks:
                outfile.write (b.name + ',')
                outfile.write (format(b.time) + ',')
                outfile.write (str(b.rule))
                outfile.write ('\n')
    print(outfile)

if __name__ == '__main__':
    ufbenchmarks = UF_BENCHMARKS
    for b in ufbenchmarks:
        b.time = run_ufbenchmark(b.name,'underlying.py')
        b.rule = open('SYPHON_LOG', "r").readlines()[-1]
    uf4benchs = UF4_BENCHMARKS
    for b in uf4benchs:
        b.time = run_ufbenchmark(b.name,'underlying-four.py')
        b.rule = open('SYPHON_LOG', "r").readlines()[-1]
    altbenchmarks = ALT_BENCHMARKS
    for b in altbenchmarks:
        b.time = run_altbenchmark(b.name,'alternation.py')
        b.rule = open('SYPHON_LOG', "r").readlines()[-1]
    supbenchs = SUP_BENCHMARKS
    for b in supbenchs:
        b.time = run_altbenchmark(b.name,'supervised.py')
        b.rule = open('SYPHON_LOG', "r").readlines()[-1]
    write_csv()




