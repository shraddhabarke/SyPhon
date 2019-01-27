import csv, unicodedata
from itertools import product

# The file where IPA data is stored.
FEATURES_FILE = '../datasets/riggle.csv'

# Map of IPA symbols to their preferred Unicode character.
IPA_NORMALIZATION = {
  'g': 'ɡ'
}

# Map from ipa symbols to feature-dicts and vice-versa. The reverse map is
# actually a map from sets of tuples, since Python doesn't provide an immutable
# dict type.
SYMBOLS_TO_FEATURES = {
  '#': {'word boundary': '+'}
}
FEATURES_TO_SYMBOLS = {
  frozenset({('word boundary', '+')}): '#'
}

# Set of feature names.
FEATURES = {'word boundary'}

# Set of IPA symbols which are diacritics, i.e., modifiers.
DIACRITICS = set()

# Map from (feature, value) pairs to weights. Lower weight means the feature
# describes more sounds.
FEATURE_WEIGHTS = {}

# Map from (feature, value) pairs to the set of (feature, value) pairs they
# imply, and vice-versa.
FEATURES_TO_IMPLICATIONS = {}
IMPLICATIONS_TO_FEATURES = {}

# Normalize an IPA string by e.g. expanding out all diacritics.
def normalize(transcription):
  symbols = unicodedata.normalize('NFD', transcription)
  return ''.join(IPA_NORMALIZATION.get(symbol, symbol) for symbol in symbols)

# Returns whether an IPA symbol is a diacritic, i.e., whether it modifies other
# symbols.
def is_diacritic(symbol):
  return symbol in DIACRITICS

# Returns the feature dict of a (non-compound) IPA symbol.
def get_features(symbol):
  return SYMBOLS_TO_FEATURES[symbol]

# Read in feature data from FEATURES_FILE.
def read_features():
  with open(FEATURES_FILE, 'r') as f:
    reader = csv.DictReader(f)
    FEATURES.update(set(reader.fieldnames) - {'symbol', 'type'})
    for row in reader:
      symbol = normalize(row.pop('symbol'))
      symbol_type = row.pop('type')
      row['word boundary'] = '-'
      SYMBOLS_TO_FEATURES[symbol] = dict(row)
      FEATURES_TO_SYMBOLS[frozenset(row.items())] = symbol
      if symbol_type == 'diacritic':
        DIACRITICS.add(symbol)

# Populate FEATURE_WEIGHTS based on features data.
def calc_weights():
  total_features = len(FEATURES_TO_SYMBOLS)
  for features in FEATURES_TO_SYMBOLS:
    for feature_value in features:
      FEATURE_WEIGHTS[feature_value] = FEATURE_WEIGHTS.get(feature_value, total_features) - 1

# Populate implications dicts using feature data.
def find_implications():
  def implies(fv1, fv2):
    for features in FEATURES_TO_SYMBOLS:
      if fv1 in features and fv2 not in features:
        return False
    return True
  fv_pairs = product(product(FEATURES, ['+', '-']), repeat=2)
  for fv1, fv2 in fv_pairs:
    if implies(fv1, fv2):
      if fv1 not in FEATURES_TO_IMPLICATIONS:
        FEATURES_TO_IMPLICATIONS[fv1] = []
      if fv2 not in IMPLICATIONS_TO_FEATURES:
        IMPLICATIONS_TO_FEATURES[fv2] = []
      FEATURES_TO_IMPLICATIONS[fv1].append(fv2)
      IMPLICATIONS_TO_FEATURES[fv2].append(fv1)

# Read feature data in and initialize all data structures.
def init():
  read_features()
  calc_weights()
  find_implications()

init()
