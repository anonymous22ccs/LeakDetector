import os
from statistics import mean
from statistics import stdev

logPaths = []
for name in os.listdir(os.getcwd()):
    if not name.endswith(".log"):
        continue
    logPath = os.path.join(os.getcwd(), name)
    logPaths.append(logPath)
logPaths.sort()

total = []
p1 = []
p2 = []
p3 = []

for logPath in logPaths:
    print logPath
    
    logFile = open(logPath, "r")
    for line in logFile.readlines():
        line = line.strip()
        if line.startswith("[Output] Process-"):
            print line
            consumption = float(line.split("spend ")[1].split(" seconds")[0].strip())
            print "\t" + str(consumption)
            if "Process-1" in line:
                p1.append(consumption)
            if "Process-2" in line:
                p2.append(consumption)
            if "Process-3" in line:
                p3.append(consumption)
    logFile.close()

for i in range(10):
    total.append(p1[i] + p2[i] + p3[i])

print mean(total)
print stdev(total)
print mean(p1)
print stdev(p1)
print (mean(p1) / mean(total)) * 100
print mean(p2)
print stdev(p2)
print (mean(p2) / mean(total)) * 100
print mean(p3)
print stdev(p3)
print (mean(p3) / mean(total)) * 100
