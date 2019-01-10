import csv, itertools, unicodedata
from demo import sat, implied_features

SYMBOL_NORMALIZATION = {
  'g': 'ɡ'
}

SYMBOL_MODIFIERS = {
  ':': {'long': '+'},
  'ʰ': {'s.g.': '+'},
  'ʻ': {'c.g.': '+'},
  '̈': {'front': '-', 'back': '-'},
  '̧': {}
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
      symbol = unicodedata.normalize('NFD', row.pop('symbol'))
      symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
      row['word boundary'] = '-'
      row['long'] = '-'
      symbols_to_features[symbol] = dict(row)

  return symbols_to_features

def get_sizes(symbols):
  feature_sizes = {}
  total_features = 0
  for symbol in symbols:
    total_features += 1
    for feature, value in symbol.items():
      feature_sizes[(feature, value)] = feature_sizes.get((feature, value), 0) + 1
  return {f: total_features - size for f, size in feature_sizes.items()}

SYMBOL_TO_FEATURES = read_features('../datasets/riggle.csv')
FEATURES_TO_SYMBOL = {frozenset(features.items()): symbol for symbol, features in SYMBOL_TO_FEATURES.items()}
FEATURE_SIZES = get_sizes(SYMBOL_TO_FEATURES.values())
FEATURES = {}
for features in SYMBOL_TO_FEATURES.values():
  FEATURES |= features.keys()
IMPLICATIONS, REVERSE_IMPLICATIONS = implied_features.get_implications(SYMBOL_TO_FEATURES.values(), FEATURES)

def triples(it):
  left, center = itertools.tee(it)
  next(center)
  center, right = itertools.tee(center)
  next(right)
  return zip(left, center, right)

def parse_grapheme(grapheme):
  symbol = ''
  features = None
  for char in list(grapheme):
    grapheme.pop(0)
    symbol += char
    normalized_symbol = SYMBOL_NORMALIZATION.get(symbol, symbol)
    if normalized_symbol in SYMBOL_TO_FEATURES:
      symbol = normalized_symbol
      break
  for char in list(grapheme):
    normalized_symbol = SYMBOL_NORMALIZATION.get(symbol + char, symbol + char)
    if normalized_symbol not in SYMBOL_TO_FEATURES:
      break
    symbol = normalized_symbol
    grapheme.pop(0)
  features = dict(SYMBOL_TO_FEATURES[symbol])
  for modifier in grapheme:
    features.update(SYMBOL_MODIFIERS[modifier])
  return features

def parse_word(word):
  graphemes = []
  for char in unicodedata.normalize('NFD', word):
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
  return sat.infer_change(changed, REVERSE_IMPLICATIONS)

def infer_rule(data, change_rule):
  return sat.infer_rule(data, change_rule, FEATURE_SIZES, FEATURES)
