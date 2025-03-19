#!/usr/bin/python

import sys
import os
import subprocess
import time
import matplotlib.pyplot as plt
import statistics

IDRIS2 = "idris2"
SAMPLES = 5
PATH_TO_CHARTS = "charts/"
RESULTS_FILE = "results.txt"

ITARATIONS = 1000
STEP = 10

INPUTS = []

def add(x, y):
    return x + y

def subtract(x, y):
    return x - y

def listOpByIndex(l1, l2, f):
    zipped = zip(l1, l2)
    diff = []
    for e1, e2 in zipped:
        diff.append(f(e1, e2))
    return diff

def exec(name, i):
    ssh = subprocess.Popen(["./build/exec/" + name],
                            stdin=subprocess.PIPE,
                            universal_newlines=True,
                            stdout=subprocess.PIPE)
    start = time.time()
    out = ssh.communicate(input=INPUTS[i])[0]
    end = time.time()
    return (end - start)

def measuretime(name, iterations):
    exec(name.lower(), 0)
    # times = [exec(name.lower(), 0)]
    times = []
    for i in range(iterations):
        times.append(exec(name.lower(), i))
    return times

def buildTimes(name, iterations):
    os.system(IDRIS2 + " -p tyre -p contrib " + name + ".idr -o " + name.lower())
    print(name, end=" ", flush=True)

    timesMatrix = []
    for i in range(SAMPLES):
        print(".", end="", flush=True)
        times = measuretime(name, iterations)
        timesMatrix.append(times)
    avg = []
    stddev = []
    for i in range(iterations):
        current = []
        for j in range(SAMPLES):
          current.append(timesMatrix[j][i])
        avg.append(statistics.mean(current))
        stddev.append(statistics.stdev(current))
    print(" done")
    return {"avg":avg, "stdev":stddev}

def runtest():
  global INPUTS
  for i in range(ITARATIONS):
    INPUTS.append("12:42" * (i * STEP))

  return {
    "auto_extract": buildTimes("TimeAutoExtract", ITARATIONS),
    "manual_extract": buildTimes("TimeManualExtract", ITARATIONS),
    "match": buildTimes("TimeMatch", ITARATIONS),
  }

def plotresult(testresult):
    auto_extract = testresult["auto_extract"]
    manual_extract = testresult["manual_extract"]
    match = testresult["match"]
    x = range(0, ITARATIONS * STEP, STEP)
    plt.plot(x, auto_extract["avg"], color='blue', label='automatic extraction')
    plt.fill_between(x,
        listOpByIndex(auto_extract["avg"], auto_extract["stdev"], subtract),
        listOpByIndex(auto_extract["avg"], auto_extract["stdev"], add),
        color='blue', alpha=0.2)
    plt.plot(x, manual_extract["avg"], color='orange', label='manual extraction')
    plt.fill_between(x,
        listOpByIndex(manual_extract["avg"], manual_extract["stdev"], subtract),
        listOpByIndex(manual_extract["avg"], manual_extract["stdev"], add),
        color='orange', alpha=0.3)
    plt.plot(x, match["avg"], color='green', label='match only')
    plt.fill_between(x,
        listOpByIndex(match["avg"], match["stdev"], subtract),
        listOpByIndex(match["avg"], match["stdev"], add),
        color='green', alpha=0.2)
    plt.ylabel('time in seconds')
    plt.xlabel("no. dates")
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + "time.png")
    plt.clf()

def runall():
    plotresult(runtest())

def setIdris(name):
    global IDRIS2
    IDRIS2 = name

def setSamples(n):
    global SAMPLES
    SAMPLES = int(n)

commands = {
    "--idris2" : setIdris,
    "--samples" : setSamples,
}

for a in sys.argv[1:]:
    cm = a.split("=")
    if len(cm) == 2 and cm[0] in commands:
        commands[cm[0]](cm[1])

if not os.path.exists(PATH_TO_CHARTS):
    os.makedirs(PATH_TO_CHARTS)

runall()
