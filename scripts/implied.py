import csv, sys, itertools

def read_phones():
	with open('../datasets/Russianriggle.csv', 'r') as infile:
		reader = csv.DictReader(infile)
		data = {}
		for row in reader:
			for header, value in row.items():
				try:
					data[header].append(value)
				except KeyError:
					data[header] = [value]
	return data

with open("../datasets/Russianriggle.csv", "r") as f:
    reader = csv.reader(f)
    cols = next(reader)

def all_same(items):
    return all(x == items[0] for x in items)

def implied(feature_1, feature_2):
	imply = []
	data = read_phones()
	f1 = data[feature_1]
	f2 = data[feature_2]
	pindices = [i for i, x in enumerate(f1) if x == "+"]
	nindices = [i for i, x in enumerate(f1) if x == "-"]
	pvalues = [f2[x] for x in pindices]
	nvalues = [f2[x] for x in nindices]
	if pvalues != [] and all_same(pvalues) and pvalues[0] != '0':
		imply.append((("+", feature_1), (pvalues[0], feature_2)))
	if nvalues != [] and all_same(nvalues) and nvalues[0] != '0':
		imply.append((("-", feature_1), (nvalues[0], feature_2)))
	return imply

def minimize(phone):
        new_features = list(phone.keys())
        for feature in phone.keys():
                new_features = [new_feature for new_feature in new_features if feature == new_feature or (((phone[feature], feature), (phone[new_feature], new_feature)) not in implied(feature, new_feature))]
        return {feature: phone[feature] for feature in new_features}

if __name__ == "__main__":
        inferred = [implied(p1, p2) for p1 in cols for p2 in cols if (p1 != p2 and p1 != 'symbol' and p2 != 'symbol')]
        result = [x for x in inferred if x != []]
