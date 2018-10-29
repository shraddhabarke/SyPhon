import csv, json, sys
if sys.argv[1] is not None and sys.argv[2] is not None:
    fileInput = sys.argv[1]
    fileOutput = sys.argv[2]
    inputFile = open(fileInput) 
    outputFile = open(fileOutput, 'w')

    data = json.load(inputFile)
    inputFile.close()

    output = csv.writer(outputFile)

    output.writerow(data[0].keys())

    for row in data:
        output.writerow(row.values())