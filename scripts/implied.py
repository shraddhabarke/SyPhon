import csv, sys, itertools

with open('/home/shraddha/Desktop/Phonosynth/datasets/riggle.csv', 'r') as infile:
  reader = csv.DictReader(infile)
  data = {}
  for row in reader:
    for header, value in row.items():
      try:
        data[header].append(value)
      except KeyError:
        data[header] = [value]

with open("/home/shraddha/Desktop/Phonosynth/datasets/riggle.csv", "r") as f:
    reader = csv.reader(f)
    cols = next(reader)

def all_same(items):
    return all(x == items[0] for x in items)

def implied(feature_1, feature_2):
	imply = []
	f1 = data[feature_1]
	f2 = data[feature_2]
	pindices = [i for i, x in enumerate(f1) if x == "+"]
	nindices = [i for i, x in enumerate(f1) if x == "-"]
	pvalues = [f2[x] for x in pindices]
	nvalues = [f2[x] for x in nindices]
	if pvalues != [] and all_same(pvalues) and pvalues[0] != '0':
		imply.append(("+"+feature_1,pvalues[0]+feature_2))
	if nvalues != [] and all_same(nvalues) and nvalues[0] != '0':
		imply.append(("-"+feature_1,nvalues[0]+feature_2))
	return imply

result = [implied(p1, p2) for p1 in cols for p2 in cols if (p1 != p2 and p1 != 'symbol' and p2 != 'symbol')]
inferred = [x for x in result if x != []]
for i in inferred:
	print(i,end="\n")


