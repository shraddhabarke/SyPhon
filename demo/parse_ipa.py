from demo import ipa_data

# Convert a list of IPA symbols to a list of lists of symbols, representing the
# individual phones. E.g. ['t', 'ʰ', 'i'] becomes [['t', 'ʰ'], ['i']].
def group_phones(symbols):
  phones = []
  for symbol in symbols:
    if ipa_data.is_diacritic(symbol):
      phones[-1].append(symbol)
    else:
      phones.append([symbol])
  return phones

# Convert a list of IPA symbols representing a single phone to a dictionary of
# features and their values.
def phone_to_features(phone):
  features = {}
  for symbol in phone:
    features.update(ipa_data.get_features(symbol))
  return features

# Convert a string representation of an IPA transcription to a list of feature
# dictionaries for each phone.
def parse(transcription):
  symbols = ipa_data.normalize(transcription)
  phones = group_phones(symbols)
  return [phone_to_features(phone) for phone in phones]
