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
YLABEL = "YLabel"
TYPE = "Type"
NUMER = "Numerator"
DENOM = "Denominator"


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


def window_mean(xs):
    ys = list(xs)
    for i in range(1, len(ys) - 1):
        ys[i] = xs[i - 1] * 0.25 + xs[i] * 0.5 + xs[i + 1] * 0.25
    ys[0] = xs[0] * 0.66 + xs[1] * 0.34
    ys[-1] = xs[-1] * 0.66 + xs[-2] * 0.34
    return ys

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
        STD_DEV: window_mean(std_dev),
    }


def read_line(indir: str, line: dict):
    if TYPE not in line:
        return read_csv(Path(indir, line[PATH]))
    elif line[TYPE] == "div":
        num = read_csv(Path(indir, line[NUMER]))
        den = read_csv(Path(indir, line[DENOM]))
        mean = window_mean([n / d for n, d in zip(num[MEAN], den[MEAN])])
        return {
            SIZE: num[SIZE],
            MEAN: mean,
            STD_DEV: [0.0 for _ in num[STD_DEV]],
        }
    else:
        raise ValueError(f"Invalid {TYPE}: {line[TYPE]}")


def draw_graph(indir: str, outdir: str, graph: dict):
    fig, ax = plt.subplots(layout="constrained")

    try:
        results = [read_line(indir, line) for line in graph[LINES]]
    except CsvException as e:
        print(f"Error reading CSV file: {e}")
        return

    size = results[0][SIZE]

    xscale = graph.get(XSCALE, 1)
    x = range(0, size * xscale + 1, xscale)

    for i, line in enumerate(graph[LINES]):
        ax.plot(x, results[i][MEAN], line[COLOR], label=line.get(LABEL))
        ax.fill_between(
            x,
            listOpByIndex(results[i][MEAN], results[i][STD_DEV], subtract),
            listOpByIndex(results[i][MEAN], results[i][STD_DEV], add),
            color=line[COLOR],
            alpha=0.2,
        )

    ax.set_ylabel(graph.get(YLABEL, "time in seconds"))
    ax.set_xlabel(graph[XLABEL])
    ax.legend(loc="upper left")

    max_y = max(y for result in results for y in result[MEAN])

    ax.set_ylim(ymin=-max_y * 0.05, ymax=max_y * 1.1)

    path = Path(outdir, graph[PATH])
    fig.savefig(path)

    print(f"Saved graph to {path}")


graphs = [
    # Staging
    {
        PATH: "staging.rep_a.png",
        LINES: [
            {PATH: "staging.rep_a_interp.csv", LABEL: "interpreted", COLOR: "blue"},
            {PATH: "staging.rep_a_compile.csv", LABEL: "staged", COLOR: "red"},
            {PATH: "staging.rep_a_ilex.csv", LABEL: "ILex", COLOR: "green"},
        ],
        XLABEL: "size of input",
        XSCALE: 1000,
    },
    {
        PATH: "staging.time.png",
        LINES: [
            {PATH: "staging.time_interp.csv", LABEL: "interpreted", COLOR: "blue"},
            {PATH: "staging.time_compile.csv", LABEL: "staged", COLOR: "red"},
            {PATH: "staging.time_ilex.csv", LABEL: "ILex", COLOR: "green"},
        ],
        XLABEL: "length of word",
        XSCALE: 5,
    },
    {
        PATH: "staging.rep_a_ratio.png",
        LINES: [
            {
                TYPE: "div",
                NUMER: "staging.rep_a_compile.csv",
                DENOM: "staging.rep_a_ilex.csv",
                COLOR: "red",
            },
        ],
        XLABEL: "size of input",
        XSCALE: 1000,
        YLABEL: "ILex speed up"
    },
    {
        PATH: "staging.time_ratio.png",
        LINES: [
            {
                TYPE: "div",
                NUMER: "staging.time_compile.csv",
                DENOM: "staging.time_ilex.csv",
                COLOR: "red",
            },
        ],
        XLABEL: "length of word",
        XSCALE: 5,
        YLABEL: "ILex speed up"
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
