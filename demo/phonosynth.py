import csv, itertools, unicodedata
from demo import sat

SYMBOL_NORMALIZATION = {
  'g': 'ɡ'
}

SYMBOL_MODIFIERS = {
  ':': {'long': '+'},
  'ʰ': {'s.g.': '+'}
}

def read_features(filename):
  symbols_to_features = {
    '#': {
      'word boundary': '+'
    }
  }
  
  with open(filename, 'r') as f:
    reader = csv.DictReader(f)
    for row in reader:
      symbol = unicodedata.normalize('NFC', row.pop('symbol'))
      symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
      row['word boundary'] = '-'
      row['long'] = '-'
      symbols_to_features[symbol] = dict(row)

  return symbols_to_features

SYMBOL_TO_FEATURES = read_features('../datasets/riggle.csv')
FEATURES_TO_SYMBOL = {frozenset(features.items()): symbol for symbol, features in SYMBOL_TO_FEATURES.items()}

def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

def parse_grapheme(grapheme):
  symbol = grapheme.pop(0)
  symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
  features = dict(SYMBOL_TO_FEATURES[symbol])
  for modifier in grapheme:
    features.update(SYMBOL_MODIFIERS[modifier])
  return features

def parse_word(word):
  graphemes = []
  for char in unicodedata.normalize('NFC', word):
    if char in SYMBOL_MODIFIERS.keys():
      graphemes[-1].append(char)
    else:
      graphemes.append([char])
  return [parse_grapheme(grapheme) for grapheme in graphemes]

def parse(words):
  data = []
  for underlying_form, realization in words:
    underlying_features = parse_word('#' + underlying_form + '#')
    realized_features = parse_word(realization)
    for i, triple in enumerate(triples(underlying_features)):
      data.append((triple, realized_features[i]))
  return data

def infer_change(data):
  changed = [(old, new) for (_, old, _), new in data if old != new]
  old, new = changed[0]
  differences = {feature: value for feature, value in new.items() if value != old[feature]}
  return differences

def infer_rule(data):
  return sat.infer_rule(data)
