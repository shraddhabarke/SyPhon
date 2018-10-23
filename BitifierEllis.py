import csv, sys
import ellis

"""
Converts a dictionary of feature values into a bitstring.

Input:
$char: Key corresponding to APA symbol in Ellis's feature inventory.

Output:
$bits: Bitstring corresponding to $char.
"""
def phone2bits(char, word):
  if char not in ellis.symbols: return "00000000000000000000000000000000000000000000000000"
  phone = ellis.symbols[char]
  bits = ""
  for f in sorted(ellis.features):
    if f in phone: bits += "1"
    else: bits += "0"
  
  print("{:24}: {:3} bitified to {}.".format(str(word), char, bits))

  return bits

def getASymbol(wordin):
  i = 0
  char = wordin[0]
  wordin = wordin[1:]
  while any(char in symbol for symbol in ellis.symbols):
    i += 1
    char += wordin[0]
    wordin = wordin[1:]
  return char[:-1]

"""
Converts a string of phonetic symbols into a list of featural bitstrings.

Input:
$word: String of phonetic symbols to be converted.

Output:
$wordout: Bit vector corresponding to $word.
"""
def bitify(word):
  print("Bitifying word: {}".format(word))
  wordin = word
  wordout = []
  bitstring = ""

  char = getASymbol(wordin)
  bitstring = phone2bits(char, word)
  wordout.append(bitstring)
  wordin = wordin[len(char):]

  while len(wordin) > 1:
    char = getASymbol(wordin)
    bitstring = phone2bits(char, word)
    wordout.append(bitstring)
    wordin = wordin[max(1, len(char)):]
 
  if word[-1] in ellis.symbols: wordout.append(phone2bits(word[-1], word))

  return wordout

filein = sys.argv[1]  # Input CSV.
bitvector = {} # Output CSV with Ellis's features.

print("String literal to bitvector conversion.")
print("Using Ellis et al.'s feature inventory in ellis.py.")
print("Features in output order are:")
print(sorted(["palatal", "palletized", "sibilant", "sonorant", "coronal", "retroflex", "creaky", "risingTone", "highTone", "lowTone", "middleTone", "long", "vowel", "tense", "lax", "high", "middle", "low", "front", "central", "back", "rounded", "bilabial", "stop", "voice", "fricative", "labiodental", "dental", "alveolar", "labiovelar", "velar", "nasal", "uvular", "glide", "liquid", "lateral", "trill", "flap", "affricate", "alveopalatal", "anterior", "aspirated", "unreleased", "laryngeal", "pharyngeal", "syllableBoundary", "wordBoundary", "continuant", "syllabic", "delayedRelease"]))

""" Read input CSV into $bitvector dictionary. """
with open(filein, "r") as f:
  print("Reading file: {}".format(filein))
  reader = csv.reader(f)
  for row in reader:
    for col in row:
      word = col
      bitvector[word] = bitify(word)
      print()

print("Bitification complete!")

""" Write $bitvector to file. """
with open(filein.split(".")[0] + "_ellis.csv", "w+") as f:
  print("Writing file: {}".format(filein.split(".")[0] + "_ellis.csv"))
  print("Features in output order are:")
  print(sorted(["palatal", "palletized", "sibilant", "sonorant", "coronal", "retroflex", "creaky", "risingTone", "highTone", "lowTone", "middleTone", "long", "vowel", "tense", "lax", "high", "middle", "low", "front", "central", "back", "rounded", "bilabial", "stop", "voice", "fricative", "labiodental", "dental", "alveolar", "labiovelar", "velar", "nasal", "uvular", "glide", "liquid", "lateral", "trill", "flap", "affricate", "alveopalatal", "anterior", "aspirated", "unreleased", "laryngeal", "pharyngeal", "syllableBoundary", "wordBoundary", "continuant", "syllabic", "delayedRelease"]))
  writer = csv.writer(f)
  for k, v in bitvector.items():
    writer.writerow([k] + v)

print("Writing complete!")
