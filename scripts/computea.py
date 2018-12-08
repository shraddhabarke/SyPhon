import csv, sys, subprocess, json
from collections import ChainMap
from strongest_classifier import weakest_classifier, strongest_sound_classifier, strongest_context_classifier, get_sat_formulas, remove_pos, read_phone, remove_indices, add_indices, get_moresat_formulas
from implied import all_same

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

def intersectdict(dict_1, dict_2):
	'''Returns intersection of dictionaries'''
	return dict(dict_1.items() & dict_2.items())

def diffdict(dict_1, dict_2):
	'''Returns the symmetric difference between dictionaries'''
	return dict(dict_1.items() ^ dict_2.items())

def mergedict(dict_1, dict_2):
	return dict(ChainMap(dict_1, dict_2))

def mod_implied(data, feature_1, feature_2, output):
	imply = []
	f1 = data[feature_1]
	f2 = data[feature_2]
	indices = [i for i, x in enumerate(f1) if (output[feature_1] != '0' and x == output[feature_1])]
	values = [f2[x] for x in indices]
	if values != [] and all_same(values) and values[0] != '0':
		imply.append((output[feature_1]+feature_1,output[feature_2]+feature_2))
	return imply

def extract_feature_value(data, dictname, featuredict):
	valuelist = list(dictname.values())
	remove_pos(data,featuredict)
	for feature, value in featuredict.items():
		llist = []
		valuelist.append(value)
		dictname.update({feature : value})
		for key, values in dictname.items():
			llist.append(data[key])
		nllist = [list(zip(*llist))[i] for i in range(len(llist[0]))]
		sindices = [i for i, x in enumerate(nllist) if (x == tuple(valuelist))]
		print(sindices)
		if(len(sindices)) == 0:
			for elem in sindices:
				print(data["symbol"][elem])
			pass
		else:
			for elem in sindices:
				print(data["symbol"][elem])
			valuelist.remove(value)
			dictname.pop(feature,None)
	return dictname

def check_noisy(data, dictname, trueneg):
	llist = []
	contextlist = []
	valuelist = list(dictname.values())
	target_indices = ([i for i, x in enumerate(data["target"]) if x == "1"])
	for feature, value in dictname.items():
		llist.append(remove_indices(target_indices, data[feature]))
	nllist = [list(zip(*llist))[i] for i in range(len(llist[0]))]
	print(nllist)
	sindices = [i for i, x in enumerate(nllist) if (x == tuple(valuelist))]
	print("The following sounds might be noisy!")
	for elem in sindices:
		print(data["symbol"][elem])
	contextvalues = list(weakcontext.values())
	for feature,value in weakcontext.items():
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
	#contextfname = sys.argv[3]
	#soundfname = sys.argv[4]
	data = read_phone(fname)
	riggledata = read_phone(riggle)
	#weakcontext = weakest_classifier(contextfname)
	#weaksound = weakest_classifier(soundfname)
	sounddict = strongest_sound_classifier(fname)
	strongcontext = strongest_context_classifier(fname)
	soundkeys = list(sounddict.keys())
	inferred = [mod_implied(riggledata, p1, p2, sounddict) for p1 in soundkeys for p2 in soundkeys if (p1 != p2 and p1 != 'symbol' and p2 != 'symbol')]
	elems = [x[0][1] for x in inferred if x != []]
	strongsound = convertlist([x for x in convertdict(sounddict) if x not in elems])
	'''
	intersect_sound = intersectdict(weaksound,strongsound)
	intersect_context = intersectdict(weakcontext,strongcontext)
	diff_sound = diffdict(weaksound,strongsound)
	diff_context = diffdict(weakcontext,strongcontext)
	print(intersect_sound,intersect_context)
	print(diff_sound, diff_context)
	check_noisy(data,strongsound,weakcontext)
	mergeddict = mergedict(intersect_sound, intersect_context)
	'''
	strongfeatures = mergedict(strongsound, strongcontext)
	print(strongfeatures)
	#remove_pos(data, mergeddict)
	#print(extract_feature_value(data, mergeddict, diff_context))
	#get_sat_formulas(fname, strongfeatures)
	get_moresat_formulas(fname, strongfeatures)