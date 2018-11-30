import csv, sys, subprocess, json
from strongest_classifier import context, classifier, read_phone, remove_indices, add_indices
from implied import all_same, inferred

def convertdict(dictname):
	clist = []
	for key,value in dictname.items():
		if(value != "0"):
			clist.append(value+key)
	return clist

def convertlist(flist):
	cdict = {}
	for elem in flist:
		cdict.update({elem[1:]:elem[0]})
	return cdict

def mod_implied(data, feature_1, feature_2, output):
	imply = []
	f1 = data[feature_1]
	f2 = data[feature_2]
	indices = [i for i, x in enumerate(f1) if (output[feature_1] != '0' and x == output[feature_1])]
	values = [f2[x] for x in indices]
	if values != [] and all_same(values) and values[0] != '0':
		imply.append((output[feature_1]+feature_1,output[feature_2]+feature_2))
	return imply

def check_noisy(data,dictname,context):
	llist = []
	contextlist = []
	valuelist = list(dictname.values())
	target_indices = ([i for i, x in enumerate(data["target"]) if x == "1"])
	for feature, value in dictname.items():
		llist.append(remove_indices(target_indices, data[feature]))
	nllist = [list(zip(*llist))[i] for i in range(len(llist[0]))]
	sindices = [i for i, x in enumerate(nllist) if (x == tuple(valuelist))]
	print("The following sounds might be noisy!")
	for elem in sindices:
		print(data["symbol"][elem])
	contextvalues = list(context.values())
	for feature,value in context.items():
		contextlist.append(add_indices(sindices, data[feature]))
	ncontextlist = [list(zip(*contextlist))[i] for i in range(len(contextlist[0]))]
	cindices = [i for i, x in enumerate(ncontextlist) if (x == tuple(contextvalues))]
	if(len(cindices)) == 0:
		print("No noise!")
	else:
		for elem in cindices:
			print(data["symbol"][elem], "is noisy!")

if __name__ == "__main__":
	fname = sys.argv[1]
	riggle = sys.argv[2]
	data = read_phone(fname)
	riggledata = read_phone(riggle)
	contextfname = sys.argv[3]
	context = context(contextfname)
	dictname = classifier(fname)
	keylist = list(dictname.keys())
	inferred = [mod_implied(riggledata, p1, p2, dictname) for p1 in keylist for p2 in keylist if (p1 != p2 and p1 != 'symbol' and p2 != 'symbol')]
	elems = [x[0][1] for x in inferred if x != []]
	computea = [x for x in convertdict(dictname) if x not in elems]
	print(context)
	check_noisy(data,convertlist(computea),context)
	print(computea)
