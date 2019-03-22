import csv, unicodedata
from itertools import product
from collections import Counter

# The file where IPA data is stored, relative to the project root.
FEATURES_FILE = 'datasets/riggle.csv'

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
FEATURES_TO_LETTERS = {
  frozenset({('word boundary', '+')}): '#'
}

# Set of feature names.
FEATURES = {'word boundary'}

# Set of IPA symbols which are diacritics, i.e., modifiers, and letters, i.e.,
# not modifiers.
DIACRITICS = set()
LETTERS = set()

# Map from (feature, value) pairs to the number of sounds they apply to.
FEATURE_WEIGHTS = Counter()

# Map from (feature, value) pairs to the set of (feature, value) pairs they
# imply, and vice-versa.
FEATURES_TO_IMPLICATIONS = {}
IMPLICATIONS_TO_FEATURES = {}

# All possible phones from our inventory.
NUM_PHONES = 0

# Normalize an IPA string by e.g. expanding out all diacritics. Converts the
# string to a list of symbols.
def normalize(transcription):
  uni_normalized = unicodedata.normalize('NFD', transcription)
  ipa_normalized = [IPA_NORMALIZATION.get(symbol, symbol) for symbol in uni_normalized]
  return ''.join(ipa_normalized)

def normalize_combining(transcription):
  def is_combining(char):
    return unicodedata.category(char)[0] == 'M'

  combining_normalized = []
  for symbol in normalize(transcription):
    if is_symbol(symbol) or not is_combining(symbol):
      combining_normalized.append(symbol)
    else:
      combined = False
      for i, existing_symbol in reversed(list(enumerate(combining_normalized))):
        if not is_combining(existing_symbol[0]):
          combined = True
          combining_normalized[i] = existing_symbol + symbol
          break
      if not combined:
        raise ValueError(f'Encountered combining character \u25cc{symbol} with no non-combining character preceding it')
  return combining_normalized

# Returns whether a string is a valid IPA symbol.
def is_symbol(symbol):
  return symbol in SYMBOLS_TO_FEATURES

# Returns whether an IPA symbol is a diacritic, i.e., whether it modifies other
# symbols.
def is_diacritic(symbol):
  return symbol in DIACRITICS

# Returns whether an IPA symbol is a letter, i.e., not a diacritic.
def is_letter(symbol):
  return symbol not in DIACRITICS

# Returns the feature dict of a (non-compound) IPA symbol.
def get_features(symbol):
  return SYMBOLS_TO_FEATURES[symbol]

# Returns the number of sounds a feature-value pair describes.
def get_weight(feature, value):
  return FEATURE_WEIGHTS[(feature, value)]

# Get the set of (feature, value) pairs which imply this feature-value pair.
def get_implying(feature, value):
  return IMPLICATIONS_TO_FEATURES.get((feature, value), frozenset())

def apply_change(change, phone):
  phone_copy = phone.copy()
  phone_copy.update(change)
  return phone_copy

# Read in feature data from FEATURES_FILE.
def read_features():
  global FEATURES
  with open(FEATURES_FILE, 'r') as f:
    reader = csv.DictReader(f)
    FEATURES.update(set(reader.fieldnames) - {'symbol', 'type'})
    FEATURES = frozenset(FEATURES)
    for row in reader:
      symbol = normalize(row.pop('symbol'))
      symbol_type = row.pop('type')
      row['word boundary'] = '-'
      features = {k: v for k, v in row.items() if v != ''}
      SYMBOLS_TO_FEATURES[symbol] = features
      FEATURES_TO_SYMBOLS[frozenset(features.items())] = symbol
      if symbol_type == 'diacritic':
        DIACRITICS.add(symbol)
      elif symbol_type == 'letter':
        LETTERS.add(symbol)
        FEATURES_TO_LETTERS[frozenset(features.items())] = symbol

# Populate FEATURE_WEIGHTS based on features data.
def calc_weights():
  global FEATURE_WEIGHTS
  FEATURE_WEIGHTS = Counter(feature_value for letter in LETTERS for feature_value in SYMBOLS_TO_FEATURES[letter].items())

# Calculate the number of distinct phones in our inventory.
def calc_num_phones():
  global NUM_PHONES
  NUM_PHONES = len(LETTERS)

# Populate implications dicts using feature data.
def find_implications():
  global FEATURES_TO_IMPLICATIONS, IMPLICATIONS_TO_FEATURES
  def implies(fv1, fv2):
    for features in FEATURES_TO_SYMBOLS:
      if fv1 in features and fv2 not in features:
        return False
    return True
  fv_pairs = product(product(FEATURES, ['+', '-']), repeat=2)
  for fv1, fv2 in fv_pairs:
    if implies(fv1, fv2):
      if fv1 not in FEATURES_TO_IMPLICATIONS:
        FEATURES_TO_IMPLICATIONS[fv1] = set()
      if fv2 not in IMPLICATIONS_TO_FEATURES:
        IMPLICATIONS_TO_FEATURES[fv2] = set()
      FEATURES_TO_IMPLICATIONS[fv1].add(fv2)
      IMPLICATIONS_TO_FEATURES[fv2].add(fv1)
  FEATURES_TO_IMPLICATIONS = {k: frozenset(v) for k, v in FEATURES_TO_IMPLICATIONS.items()}
  IMPLICATIONS_TO_FEATURES = {k: frozenset(v) for k, v in IMPLICATIONS_TO_FEATURES.items()}

# Read feature data in and initialize all data structures.
def init():
  read_features()
  calc_weights()
  calc_num_phones()
  find_implications()

init()
