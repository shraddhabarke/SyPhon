import csv, sys, subprocess, json
from implied import all_same, read_phones, inferred

def convertdict(dictname):
	clist = []
	for key,value in dictname.items():
		if(value != "0"):
			clist.append(value+key)
	return clist

def mod_implied(feature_1, feature_2,output):
	data = read_phones()
	imply = []
	f1 = data[feature_1]
	f2 = data[feature_2]
	indices = [i for i, x in enumerate(f1) if (output[feature_1] != '0' and x == output[feature_1])]
	values = [f2[x] for x in indices]
	if values != [] and all_same(values) and values[0] != '0':
		imply.append((output[feature_1]+feature_1,output[feature_2]+feature_2))
	return imply

if __name__ == "__main__":
  dictname = json.loads(sys.argv[1])
  dictlist = list(dictname.keys())
  inferred = [mod_implied(p1, p2,dictname) for p1 in dictlist for p2 in dictlist if (p1 != p2 and p1 != 'symbol' and p2 != 'symbol')]
  elems = [x[0][1] for x in inferred if x != []]
  computea = [x for x in convertdict(dictname) if x not in elems]
  print(computea)




