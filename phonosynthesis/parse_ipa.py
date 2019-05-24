import unicodedata
from phonosynthesis import ipa_data
from phonosynthesis.phone import Phone

# Convert a list of IPA symbols to a list of lists of symbols, representing the
# individual phones. E.g. ['t', 'ʰ', 'i'] becomes [['t', 'ʰ'], ['i']].
def group_phones(symbols):
  phones = []
  for symbol in symbols:
    if ipa_data.is_diacritic(symbol):
      phones[-1].append(symbol)
    elif ipa_data.is_delimiter(symbol):
      continue
    elif ipa_data.is_letter(symbol):
      phones.append([symbol])
    elif symbol.isspace():
      continue
    else:
      formatted_symbol = (symbol, [unicodedata.name(char) for char in symbol])
      raise LookupError(f'Symbol not in inventory: {formatted_symbol}')
  return phones

# Convert a list of IPA symbols representing a single phone to a dictionary of
# features and their values.
def phone_to_features(phone):
  features = Phone(phone)
  for symbol in phone:
    features.update(ipa_data.get_features(symbol))
  return features

# Convert a string representation of an IPA transcription to a list of feature
# dictionaries for each phone.
def parse(transcription):
  symbols = ipa_data.normalize_combining(transcription)
  phones = group_phones(symbols)
  return [phone_to_features(phone) for phone in phones]
