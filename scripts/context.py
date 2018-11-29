#! /usr/bin/env python3

"""Generate [language_name]context.csv file (similar to Gencontext[l-r].csv and Russiancontext.csv) for a specific language
(need a better description)
"""

# usage example: python3 context.py ../datasets/AmharicIPA.csv
# [Language]IPA.csv files can be found in the Dataset Files folder in the Team Drive
from itertools import tee

import riggle, argparse, csv


def tuplewise(iterable):
    "s -> (s0,s1,s2), (s1,s2,s3), (s2, s3,4), ..."
    a, b, c = tee(iterable, 3)
    next(b, None)
    next(c, None)
    next(c, None)
    return zip(a, b, c)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input_csv_file', help='an csv file where the first column are words in IPA symbols')
    args = parser.parse_args()

    triplets = set()
    with open(args.input_csv_file)as f:
        for line in csv.reader(f):
            word, _ = line
            triplets.update(tuplewise('#' + word + '#'))

    # hard-coded order
    features = ["voice", "front", "nas", "back", "round", "cons", "cont", "coronal", "ATR", "dist",
                "del. rel.", "c.g.", "approx", "labial", "high", "strid", "ant", "dorsal", "s.g.", "son", "lat", "syll",
                "low"]

    unknown_symbols = set()

    def features_vector(s):
        if s in symbol_dict:
            return [symbol_dict[s][f] for f in features]
        elif s == '#':
            return ['#' for f in features]
        else:
            unknown_symbols.add(s)
            return ['?' for f in features]

    symbol_dict = {}
    for sym in riggle.symbols:
        symbol_dict[sym['symbol']] = sym

    headings = ['context'] + features + ['L' + f for f in features] + ['R' + f for f in features]
    print(','.join(headings))

    for l, m, r in triplets:
        # left, middle, right

        fv = ['{} {}_{}'.format(m, l, r)] + features_vector(m) + features_vector(l) + features_vector(r)
        print(','.join(fv))

    print('Unknown symbols:' + ','.join(unknown_symbols))


if __name__ == '__main__':
    main()
