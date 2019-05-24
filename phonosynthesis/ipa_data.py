import csv, unicodedata, math
from itertools import product
from collections import Counter
from phonosynthesis import parse_ipa

# The file where IPA data is stored, relative to the project root.
FEATURES_FILE = 'datasets/riggle.csv'

# Map of IPA symbols to their preferred Unicode character.
IPA_NORMALIZATION = {
  'g': 'ɡ',
  'ɩ': 'ɪ',
  'ɜ': 'ə'
}

# Map from ipa symbols to feature-dicts and vice-versa. The reverse map is
# actually a map from sets of tuples, since Python doesn't provide an immutable
# dict type.
SYMBOLS_TO_FEATURES = {}
FEATURES_TO_SYMBOLS = {}
FEATURES_TO_LETTERS = {}
LETTERS_TO_FEATURES = {}

# Set of feature names.
FEATURES = set()

# Set of IPA symbols which are diacritics (modifiers), letters (complete
# sounds), and delimiters.
DIACRITICS = set()
LETTERS = set()
DELIMITERS = set()

# Map from (feature, value) pairs to the number of sounds they apply to.
FEATURE_WEIGHTS = Counter()
FEATURE_SIMPLICITY = {}

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

def matches(features, partial_features):
  for feature, value in partial_features.items():
    if features[feature] != value:
      return False
  return True

# Returns the set of letters which match a feature vector
def get_matching_letters(features):
  matching_letters = set()
  for letter, letter_features in LETTERS_TO_FEATURES.items():
    if matches(letter_features, features):
      matching_letters.add(letter)
  return matching_letters

# Returns the single letter which matches a feature vector, if any
def get_matching_letter(features):
  for feature, value in features.items():
    for diacritic in DIACRITICS:
      diacritic_features = SYMBOLS_TO_FEATURES[diacritic]
      if feature in diacritic_features and diacritic_features[feature] == value:
        return None
  matching_letters = get_matching_letters(features)
  if len(matching_letters) == 1:
    return next(iter(matching_letters))
  else:
    return None


# Returns whether a string is a valid IPA symbol.
def is_symbol(symbol):
  return symbol in SYMBOLS_TO_FEATURES

# Returns whether an IPA symbol is a diacritic, i.e., whether it modifies other
# symbols.
def is_diacritic(symbol):
  return symbol in DIACRITICS

# Returns whether an IPA symbol is a letter, i.e., it represents a complete sound
def is_letter(symbol):
  return symbol in LETTERS

# Returns whether an IPA symbol is a delimiter (for syllables etc.)
def is_delimiter(symbol):
  return symbol in DELIMITERS

# Returns the feature dict of a (non-compound) IPA symbol.
def get_features(symbol):
  return SYMBOLS_TO_FEATURES[symbol]

# Returns the number of sounds a feature-value pair describes.
def get_weight(feature, value):
  return FEATURE_WEIGHTS[(feature, value)]

# Get the set of (feature, value) pairs which imply this feature-value pair.
def get_implying(feature, value):
  return IMPLICATIONS_TO_FEATURES.get((feature, value), frozenset())

# Get the set of (feature, value) pairs which are implied by this feature-value pair.
def get_implied(feature, value):
  return FEATURES_TO_IMPLICATIONS.get((feature, value), frozenset())

def implies(feature1, value1, feature2, value2):
  return (feature2, value2) in get_implied(feature1, value1)

# Deprecated, use Change.apply
def apply_change(change, phone):
  phone_copy = phone.copy()
  phone_copy.update(change)
  for feature, value in phone_copy.items():
    if (feature, value) in FEATURES_TO_IMPLICATIONS:
      implied = FEATURES_TO_IMPLICATIONS[(feature, value)]
      for (other_feature, other_value) in implied:
        phone_copy[other_feature] = other_value
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
      features = {k: v for k, v in row.items() if v != ''}
      SYMBOLS_TO_FEATURES[symbol] = features
      FEATURES_TO_SYMBOLS[frozenset(features.items())] = symbol
      if symbol_type == 'diacritic':
        DIACRITICS.add(symbol)
      elif symbol_type == 'letter':
        LETTERS.add(symbol)
        LETTERS_TO_FEATURES[symbol] = features
        FEATURES_TO_LETTERS[frozenset(features.items())] = symbol
      elif symbol_type == 'delimiter':
        DELIMITERS.add(symbol)

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
  for (f1, v1), (f2, v2) in fv_pairs:
    skip = False
    for diacritic in DIACRITICS:
      diacritic = SYMBOLS_TO_FEATURES[diacritic]
      if (f1 in diacritic and diacritic[f1] == v1) or (f2 in diacritic and diacritic[f2] != v2):
        skip = True
        break
    if skip:
      continue
    if implies((f1, v1), (f2, v2)):
      if (f1, v1) not in FEATURES_TO_IMPLICATIONS:
        FEATURES_TO_IMPLICATIONS[(f1, v1)] = set()
      if (f2, v2) not in IMPLICATIONS_TO_FEATURES:
        IMPLICATIONS_TO_FEATURES[(f2, v2)] = set()
      FEATURES_TO_IMPLICATIONS[(f1, v1)].add((f2, v2))
      IMPLICATIONS_TO_FEATURES[(f2, v2)].add((f1, v2))
  FEATURES_TO_IMPLICATIONS = {k: frozenset(v) for k, v in FEATURES_TO_IMPLICATIONS.items()}
  IMPLICATIONS_TO_FEATURES = {k: frozenset(v) for k, v in IMPLICATIONS_TO_FEATURES.items()}

def format_rule(target, context, change):
  def format_features(features):
    matching_letter = get_matching_letter(features)
    if matching_letter:
      return matching_letter
    elif len(features) == 0:
      return '_'
    else:
      fvec = ' '.join([f'{value}{feature}' for feature, value in features.items()])
      return f'[{fvec}]'

  displayed_change = {}
  for feature, value in change.simplified_change.items():
    if change.is_contextual(feature):
       displayed_change[feature] = 'α'
       context[value][feature] = 'α'
    else:
      displayed_change[feature] = value

  if target.keys() & change.simplified_change.keys():
    for feature in change.simplified_change.keys():
      target.pop(feature, None)

  return f'{format_features(target)} → {format_features(displayed_change)} / {format_features(context["left"])} _ {format_features(context["right"])}'

def calc_feature_simplicity():
  global FEATURE_SIMPLICITY
  for feature in FEATURES:
    zeros = 0
    for fv in LETTERS_TO_FEATURES.values():
      if fv[feature] == '0':
        zeros += 1
    FEATURE_SIMPLICITY[feature] = math.floor(100 * math.log(zeros + 1))

EMPTY_PHONE = None

def get_empty_phone():
  global EMPTY_PHONE
  if not EMPTY_PHONE:
    EMPTY_PHONE = parse_ipa.parse('∅')[0]
  return EMPTY_PHONE

# Read feature data in and initialize all data structures.
def init():
  read_features()
  calc_weights()
  calc_num_phones()
  calc_feature_simplicity()
  find_implications()

init()
