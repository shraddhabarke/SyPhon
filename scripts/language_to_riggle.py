#! /usr/bin/env python3

"""Generate [language_name]riggle.csv file (similar to riggle.csv) for a specific language,
 by removing phonetic symbols not in the language from riggle.py/riggle.csv"""

# usage example: python3 language_to_riggle.py ../datasets/AmharicAPA.csv
# [Language]APA.csv files can be found in the Dataset Files folder in the Team Drive

import riggle, argparse, csv

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('input_csv_file', help='an csv file where the first column are words in IPA symbols')
    args = parser.parse_args()

    symbols = set()
    with open(args.input_csv_file)as f:
        for line in csv.reader(f):
            phone, meaning = line
            symbols.update(phone)

    features = ["symbol","voice", "front", "nas", "back", "round", "cons", "cont", "coronal", "ATR", "dist",
                "del. rel.", "c.g.", "approx", "labial", "high", "strid", "ant", "dorsal", "s.g.", "son", "lat", "syll",
                "low"]

    print(','.join(features))
    for sym in riggle.symbols:
        if sym['symbol'] in symbols:
            print(','.join(sym[f] for f in features))

if __name__ == '__main__':
    main()
