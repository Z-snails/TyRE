from argparse import ArgumentParser
import csv
from pathlib import Path
import matplotlib.pyplot as plt

NAME = "Name"
MEAN = "Mean"
STD_DEV = "StdDev"
SIZE = "Size"
PATH = "Path"
LINES = "Lines"
LABEL = "Label"
COLOR = "Color"
XLABEL = "XLabel"
XSCALE = "XScale"


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


class CsvException(Exception):
    pass


def read_csv(fp: Path):
    name, size = None, None

    try:
        with open(fp) as f:
            reader = csv.DictReader(f, lineterminator="\n")
            mean = []
            std_dev = []
            for record in reader:
                name = record[NAME]
                size = int(record[SIZE])
                mean.append(float(record[MEAN]))
                std_dev.append(float(record[STD_DEV]))
    except IOError as e:
        raise CsvException(f"Could not read file: {fp}\n  {e}")

    if name == None or size == None:
        raise CsvException(f"Invalid CSV: {fp}")

    return {
        NAME: name,
        SIZE: size,
        MEAN: mean,
        STD_DEV: std_dev,
    }


def draw_graph(indir: str, outdir: str, graph: dict):
    fig, ax = plt.subplots()

    try:
        results = [read_csv(Path(indir, line[PATH])) for line in graph[LINES]]
    except CsvException as e:
        print(f"Error reading CSV file: {e}")
        return

    max = results[0][SIZE]

    xscale = graph.get(XSCALE, 1)
    x = range(0, max * xscale + 1, xscale)

    for i, line in enumerate(graph[LINES]):
        ax.plot(x, results[i][MEAN], line[COLOR], label=line[LABEL])
        ax.fill_between(
            x,
            listOpByIndex(results[i][MEAN], results[i][STD_DEV], subtract),
            listOpByIndex(results[i][MEAN], results[i][STD_DEV], add),
            color=line[COLOR],
            alpha=0.2,
        )

    ax.set_ylabel("time in seconds")
    ax.set_xlabel(graph[XLABEL])
    ax.legend(loc="upper left")

    path = Path(outdir, graph[PATH])
    fig.savefig(path)

    print(f"Saved graph to {path}")


graphs = [
    # Staging
    {
        PATH: "staging.rep_a.png",
        LINES: [
            {PATH: "staging.rep_a_interp.csv", LABEL: "a* interpreted", COLOR: "blue"},
            {PATH: "staging.rep_a_compile.csv", LABEL: "a* staged", COLOR: "red"},
        ],
        XLABEL: "size of input",
        XSCALE: 1000,
    },
    {
        PATH: "staging.time.png",
        LINES: [
            {PATH: "staging.time_interp.csv", LABEL: "interpreted", COLOR: "blue"},
            {PATH: "staging.time_compile.csv", LABEL: "staged", COLOR: "red"},
        ],
        XLABEL: "length of word",
        XSCALE: 5,
    },
    # Group
    {
        PATH: "group.png",
        LINES: [
            {PATH: "group.comb.csv", LABEL: "parser combinators", COLOR: "orange"},
            {PATH: "group.re_unbalanced.csv", LABEL: "TyRE unbalanced", COLOR: "blue"},
            {PATH: "group.re_balanced.csv", LABEL: "TyRE balanced", COLOR: "magenta"},
            {
                PATH: "group.re_unbalanced_group.csv",
                LABEL: "TyRE unbalanced group",
                COLOR: "red",
            },
            {
                PATH: "group.re_balanced_group.csv",
                LABEL: "TyRE balanced group",
                COLOR: "green",
            },
        ],
        XLABEL: "alt group",
    },
    # Times
    {
        PATH: "time.png",
        LINES: [
            {PATH: "time.auto.csv", LABEL: "automatic extraction", COLOR: "orange"},
            {PATH: "time.manual.csv", LABEL: "manual extraction", COLOR: "blue"},
            {PATH: "time.match.csv", LABEL: "match only", COLOR: "green"},
        ],
        XLABEL: "length of word",
        XSCALE: 5,
    },
    # Misc
    {
        PATH: "concat.png",
        LINES: [
            {PATH: "concat_tyre.csv", LABEL: "TyRE", COLOR: "blue"},
            {PATH: "concat_comb.csv", LABEL: "parser combinators", COLOR: "orange"},
        ],
        XLABEL: "length of regex and word",
    },
    {
        PATH: "star.png",
        LINES: [
            {PATH: "star_tyre.csv", LABEL: "TyRE", COLOR: "blue"},
            {PATH: "star_comb.csv", LABEL: "parser combinators", COLOR: "orange"},
        ],
        XLABEL: "length of word",
    },
    {
        PATH: "star2.png",
        LINES: [
            {PATH: "star_tyre2.csv", LABEL: "TyRE", COLOR: "blue"},
            {PATH: "star_comb2.csv", LABEL: "parser combinators", COLOR: "orange"},
        ],
        XLABEL: "length of word",
    },
    {
        PATH: "alternation.png",
        LINES: [
            {PATH: "alt_tyre.csv", LABEL: "TyRE", COLOR: "blue"},
            {PATH: "alt_comb.csv", LABEL: "parser combinators", COLOR: "orange"},
        ],
        XLABEL: "length of regex",
    },
]

if __name__ == "__main__":
    parser = ArgumentParser()
    parser.add_argument("--results-dir", default="results", dest="indir")
    parser.add_argument("--output-dir", default="charts", dest="outdir")
    args = parser.parse_args()

    for graph in graphs:
        draw_graph(args.indir, args.outdir, graph)
