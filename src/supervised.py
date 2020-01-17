import phonosynth, ipa_data
import csv, z3, sys, argparse

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

def create_word(fname):
    word = []
    with open(fname) as rf:
        reader = csv.reader(rf)
        for row in reader:
            word.append(row)
    return word

def get_rules(words):
    data = phonosynth.parse(words)
    changes = phonosynth.infer_change(data)
    rules = phonosynth.infer_rule(data, changes)
    return rules

if __name__ == "__main__":
    words = create_word(fname)
    rule = get_rules(words)
    print(rule)