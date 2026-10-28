"""Plot the baseline polylines and the retained rational concave fits."""
import argparse
from fractions import Fraction
import json
import os
from pathlib import Path

task_config = Path(__file__).resolve().parents[1] / ".tmp" / "matplotlib"
task_config.mkdir(parents=True, exist_ok=True)
os.environ.setdefault("MPLCONFIGDIR", str(task_config))
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--results", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    report = json.loads(args.results.read_text(encoding="utf-8"))
    region = report["smaller_regions"]["100000"]
    selected = report["selection_100000"]
    names = {"affine_fit": "affine", "log_affine_fit": "log-affine",
             "concave_quadratic_fit": "concave quadratic"}
    colors = {"affine_fit": "#c47719", "log_affine_fit": "#2172a0",
              "concave_quadratic_fit": "#a53458"}
    fig, axes = plt.subplots(1, 3, figsize=(15, 5.4), constrained_layout=True)
    fig.suptitle("Concave fits above logarithmic witness polylines", fontsize=17)
    for ax, key, title in zip(axes, ("negative", "non_one", "mr"),
                              (r"$Q_{-1}$", r"$Q_{\neq 1}$", "Miller–Rabin")):
        fit = region[key]
        points = np.array([[float(Fraction(x)), float(Fraction(y))]
                           for x, y in fit["baseline_polyline"]])
        left, right = map(lambda x: float(Fraction(x)), fit["domain_L_rational_cover"])
        grid = np.linspace(left, right, 2000)
        cap = points[-1, 1]
        values = []
        ax.plot(points[:, 0], points[:, 1], "o--", color="#777777", linewidth=1.5,
                markersize=4.5, label="baseline polyline", zorder=6)
        for name in selected[key]["retained"]:
            data = fit[name]
            a, b, c = [float(Fraction(data[s])) for s in ("alpha", "beta", "gamma")]
            y = (a * grid - b * grid**2 + c if name == "concave_quadratic_fit"
                 else a * grid + b * np.log(grid) + c)
            y = np.minimum(cap, y)
            values.append(y)
            ax.plot(grid, y, color=colors[name], linewidth=1.3, alpha=0.85, label=names[name])
        envelope = np.min(values, axis=0)
        baseline = np.interp(grid, points[:, 0], points[:, 1])
        ax.fill_between(grid, baseline, envelope, color="#93b5c4", alpha=0.18)
        ax.plot(grid, envelope, color="#182730", linewidth=2.7, label="retained envelope", zorder=5)
        ax.set_title(title, fontsize=16, pad=12)
        ax.set_xlabel(r"$L=\ln n$", fontsize=13)
        ax.set_ylabel("least witness: running maximum", fontsize=11)
        ax.set_xlim(left, right)
        ax.set_ylim(0 if key != "mr" else 1.7, cap * 1.08)
        ax.grid(alpha=0.22)
        ax.legend(loc="upper left", fontsize=9.5, framealpha=0.95)
        ax.text(0.98, 0.04, r"$n\leq 10^5$", transform=ax.transAxes,
                ha="right", fontsize=12, color="#485961")
    args.output.mkdir(parents=True, exist_ok=True)
    for extension in ("svg", "png"):
        path = args.output / f"fits_L_100000.{extension}"
        fig.savefig(path, dpi=180)
        print(path, flush=True)


if __name__ == "__main__":
    main()
