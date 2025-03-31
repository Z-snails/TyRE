from argparse import ArgumentParser
from dataclasses import dataclass
from pathlib import Path
import os
import subprocess


@dataclass
class Config:
    exe: str
    outdir: Path
    max: int
    samples: int

    def out_path(self, name: str):
        return Path(self.outdir, f"{name}.csv")

    def run_benchmark(self, name: str, index: int, count: int):
        out = self.out_path(name)

        if out.exists():
            print(f"Skipping {name} ({index + 1} / {count}) (already benchmarked)")
            return

        print(f"Running benchmark {name} ({index + 1} / {count})")
        os.makedirs(self.outdir, exist_ok=True)
        res = subprocess.run(
            [self.exe, name, "--max", str(self.max), "--samples", str(self.samples)],
            stdout=subprocess.PIPE,
        )
        if res.returncode != 0:
            print(f"Test {name} failed - code: {res.returncode}")
        with open(out, mode="wb") as f:
            f.write(res.stdout)

    def get_benchmarks(self):
        p = subprocess.run([self.exe, "list"], stdout=subprocess.PIPE, encoding="utf8")
        return p.stdout.splitlines()

    def run_all(self):
        benchs = self.get_benchmarks()
        print(f"Running {len(benchs)} benchmarks")
        for i, bench in enumerate(benchs):
            self.run_benchmark(bench, i, len(benchs))

    @staticmethod
    def parse():
        parser = ArgumentParser()
        parser.add_argument("--exe", default="./build/exec/bench")
        parser.add_argument("--output-dir", "-o", type=Path, default="results")
        parser.add_argument("--max", type=int, default=1000)
        parser.add_argument("--samples", type=int, default=20)
        args = parser.parse_args()
        return Config(
            args.exe, Path(args.output_dir).absolute(), args.max, args.samples
        )


if __name__ == "__main__":
    config = Config.parse()
    print(config)
    config.run_all()
