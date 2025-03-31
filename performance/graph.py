from argparse import ArgumentParser
import json
from pathlib import Path
import matplotlib.pyplot as plt

PATH_TO_CHARTS = "charts/"

NAME = "name"
TYRE_FILE = "tyreFile"
COMB_FILE = "combFile"
XLABEL = "xlabel"


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


def plotresult(test, testresult):
    tyretimes = testresult["tyretimes"]
    combtimes = testresult["combtimes"]
    x = range(1, tyretimes["config"]["iterations"] + 1)
    plt.plot(x, tyretimes["avg"], color="blue", label="TyRE")
    plt.fill_between(
        x,
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], subtract),
        listOpByIndex(tyretimes["avg"], tyretimes["stdev"], add),
        color="blue",
        alpha=0.2,
    )
    plt.plot(x, combtimes["avg"], color="orange", label="parser combinators")
    plt.fill_between(
        x,
        listOpByIndex(combtimes["avg"], combtimes["stdev"], subtract),
        listOpByIndex(combtimes["avg"], combtimes["stdev"], add),
        color="orange",
        alpha=0.3,
    )
    plt.ylabel("time in seconds")
    plt.xlabel(test[XLABEL])
    plt.legend(loc="upper left")
    plt.savefig(PATH_TO_CHARTS + test[NAME] + ".png")
    plt.clf()


tests = [
    {
        NAME: "star",
        TYRE_FILE: "StarTyRE",
        COMB_FILE: "StarComb",
        XLABEL: "length of word",
    },
    {
        NAME: "star2",
        TYRE_FILE: "StarTyRE2",
        COMB_FILE: "StarComb2",
        XLABEL: "length of word",
    },
    {
        NAME: "concat",
        TYRE_FILE: "ConcatTyRE",
        COMB_FILE: "ConcatComb",
        XLABEL: "length of regex and word",
    },
    {
        NAME: "alternation",
        TYRE_FILE: "AltTyRE",
        COMB_FILE: "AltComb",
        XLABEL: "length of regex",
    },
]


def plot_all(tests, data_dir):
    for test in tests:
        tyre_file = f"{test[TYRE_FILE].lower()}_results.json"
        comb_file = f"{test[COMB_FILE].lower()}_results.json"
        with (
            open(Path(data_dir, tyre_file)) as tyre,
            open(Path(data_dir, comb_file)) as comb,
        ):
            testresult = {"tyretimes": json.load(tyre), "combtimes": json.load(comb)}
            plotresult(test, testresult)

if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--data-dir", type=str, default="data")

    args = parser.parse_args()
    data_dir = args.data_dir

    plot_all(tests, data_dir)
