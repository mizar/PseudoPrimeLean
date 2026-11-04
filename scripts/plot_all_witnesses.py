#!/usr/bin/env python3
"""Plot the published witness record points using only the public CSV files."""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FixedLocator, FuncFormatter, LogLocator, NullFormatter


ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "scripts" / "data"
SERIES = (
    ("mr_records.csv", "o", r"MR witness $q_{\mathrm{MR}}(n)$"),
    ("negative_records.csv", "s", r"Negative witness $q_{-1}(n)$"),
    ("non_one_records.csv", "^", r"Non-1 witness $q_{\neq 1}(n)$"),
)


def read_records(path: Path) -> list[tuple[int, int]]:
    with path.open(encoding="utf-8-sig", newline="") as source:
        records = [(int(row["n"]), int(row["witness"])) for row in csv.DictReader(source)]
    if not records or any(n <= 1 or witness <= 0 for n, witness in records):
        raise ValueError(f"Invalid or empty record data: {path}")
    if any(a[0] >= b[0] or a[1] >= b[1] for a, b in zip(records, records[1:])):
        raise ValueError(f"Record inputs and witnesses must increase: {path}")
    return records


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "doc" / "figures")
    parser.add_argument("--format", choices=("png", "svg"), help="Output only this format")
    args = parser.parse_args()

    datasets = [(read_records(DATA / filename), marker, label) for filename, marker, label in SERIES]
    fig, ax = plt.subplots(figsize=(10.5, 7.5))
    for records, marker, label in datasets:
        x = [math.log(n) for n, _ in records]
        y = [witness for _, witness in records]
        ax.step(x, y, where="post", marker=marker, markersize=5, label=label)

    xmin = min(math.log(records[0][0]) for records, _, _ in datasets)
    xmax = max(math.log(records[-1][0]) for records, _, _ in datasets)
    x = np.geomspace(xmin, xmax, 400)
    ax.plot(x, x**2, "r--", label=r"$f(n)=(\ln n)^2$")
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlabel(r"$n$", fontsize=12)
    ax.set_ylabel("witness", fontsize=12)
    ax.set_title("Witness update points", fontsize=16, pad=10)
    max_exponent = math.ceil(xmax / math.log(10))
    exponents = [k for k in range(1, max_exponent + 1) if k <= 10 or k % 2 == 0]
    ax.xaxis.set_major_locator(FixedLocator([k * math.log(10) for k in exponents]))
    ax.xaxis.set_major_formatter(FuncFormatter(lambda value, _: rf"$10^{{{round(value / math.log(10))}}}$"))
    ax.xaxis.set_minor_locator(LogLocator(base=10, subs=np.arange(2, 10)))
    ax.xaxis.set_minor_formatter(NullFormatter())
    ax.tick_params(axis="x", labelrotation=-90)
    ax.grid(True, which="major", alpha=0.25)
    ax.legend(loc="upper left")
    top = ax.secondary_xaxis("top")
    top.set_xlabel(r"positioned by $\ln n$")
    fig.tight_layout()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for output_format in (args.format,) if args.format else ("svg", "png"):
        output = args.output_dir / f"all_witnesses.{output_format}"
        fig.savefig(output, dpi=100)
        if output_format == "svg":
            output.write_text("\n".join(line.rstrip() for line in
                                        output.read_text(encoding="utf-8").splitlines()) + "\n",
                              encoding="utf-8", newline="\n")
        print(output)
    plt.close(fig)


if __name__ == "__main__":
    main()
