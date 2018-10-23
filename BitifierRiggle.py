import csv, sys
import riggle

"""
Converts a dictionary of feature values into a bitstring.

Input:
$phone: Dictionary of feature values for a given phone.

Output:
$bits: Bitstring corresponding to $phone.
"""
def phone2bits(phone, word):
  bits = ""
  for k, v in sorted(phone.items()):
    if v == "0" or v == "-": bits += "0" # Feature is − or unspecified.
    elif v == "+": bits += "1"           # Feature is +.
    else: bits += ""                     # Skip if k = "symbol".
  
  print("{:24}: {:3} bitified to {}.".format(word, phone["symbol"], bits))

  return bits

"""
Converts a string of phonetic symbols into a list of featural bitstrings.

Input:
$word: String of phonetic symbols to be converted.

Output:
$wordout: Bit vector corresponding to $word.
"""
def bitify(word):
  print("Bitifying word: {}".format(word))
  wordout = []
  for char in word:                         # Iterate over each character.
    bitstring = "00000000000000000000000"   # Start with an `empty' bitstring.
    for phone in riggle.symbols:            # Iterate over each phone in riggle.py's feature inventory.
      if phone["symbol"] == char:           # Found the matching phone!
        bitstring = phone2bits(phone, word) # Now, bitify it.
    wordout.append(bitstring)               # Finally, add it to the bitvector.
  return wordout

filein = sys.argv[1]  # Input CSV.
bitvector = {} # Output CSV with Riggle's features.

print("String literal to bitvector conversion.")
print("Using Riggle et al.'s feature inventory in riggle.py.")
print("Features in output order are:")
print(sorted(["voice", "front", "nas", "back", "round", "cons", "cont", "coronal", "ATR", "dist", "symbol", "del. rel.", "c.g.", "approx", "labial", "high", "strid", "ant", "dorsal", "s.g.", "son", "lat", "syll", "low"]))

""" Read input CSV into both bitvector dictionaries. """
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
with open(filein.split(".")[0] + "_riggle.csv", "w+") as f:
  print("Writing file: {}".format(filein.split(".")[0] + "_riggle.csv"))
  writer = csv.writer(f)
  for k, v in bitvector.items():
    writer.writerow([k] + v)

print("Writing complete!")
