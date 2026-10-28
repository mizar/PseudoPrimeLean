#!/usr/bin/env python3
"""Plot the QNeOne comparison in doc/PseudoSquare.md using Matplotlib.

Install matplotlib, then run this script from any directory. The horizontal
coordinate is ln(ln B), but tick labels show B as powers of ten. No enormous B
values are constructed: all analytic calculations use L = ln B.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator


ROOT = Path(__file__).resolve().parents[1]
DATA_DIR = Path(__file__).resolve().parent / "data"
KAPPA = 0.01 / (1 + math.sqrt(0.99))


def crossing() -> float:
    """Crossing of the double-logarithm radius and the two-pole radius."""
    lo, hi = 500.0, 800.0
    for _ in range(100):
        mid = (lo + hi) / 2
        T = mid - 2 * math.log(mid) + 37 / 5
        V = (99 / 40) * ((500 / 821) * (mid + 7 / 5) + 213 / 20)**2
        if T*T < V:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def upper(L: np.ndarray) -> np.ndarray:
    """Published bounds, extended to real B for drawing; theorems use natural B."""
    baseline = np.select(
        [L < math.log(10), L < math.log(2984), L < math.log(3295),
         L < 12.5, L <= math.exp(3.5), L < 96, L < 290, L < 800, L < 22221],
        [np.full_like(L, 5), L**2, (L - 0.001)**2, (L - 0.1)**2,
         (L - 0.5)**2, (L - np.log(L) + 3)**2,
         (L - np.log(L) + 11 / 4)**2,
         np.minimum((L - np.log(L) + 11 / 4)**2, .99 * L**2),
         (99 / 40) * ((500 / 821) * (L + 7 / 5) + 213 / 20)**2],
        default=.8 * L**2,
    )
    previous = np.minimum(np.minimum(baseline, np.where(L >= 50,
        (L - 2 * np.log(L) + 37 / 5)**2, np.inf)), np.where(L >= 500,
        (99 / 40) * ((500 / 821) * (L + 7 / 5) + 213 / 20)**2, np.inf))
    return np.minimum(previous, np.where(
        (L >= 3259 / 25) & (L <= 16277 / 100),
        ((3200 / 3241) * (L - 18 / 25))**2, np.inf))


def power_ticks(ax: plt.Axes, powers: list[int]) -> None:
    ax.xaxis.set_major_locator(FixedLocator([math.log(k * math.log(10)) for k in powers]))
    ax.xaxis.set_major_formatter(FuncFormatter(
        lambda x, _: rf"$10^{{{round(math.exp(x) / math.log(10))}}}$"))
    ax.xaxis.set_minor_locator(NullLocator())


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "doc/figures")
    parser.add_argument("--max-power", type=int, default=16384,
                        help="Right endpoint B = 10**max_power (default: 16384).")
    args = parser.parse_args()
    if args.max_power < 400:
        parser.error("--max-power must be at least 400 to show the final crossover")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 11, "svg.hashsalt": "qne1-comparison",
                         "axes.spines.top": False, "axes.spines.right": False})

    root = crossing()
    Lmax = args.max_power * math.log(10)
    boundaries = [math.log(3), math.log(10), math.log(2984), math.log(3295),
                  12.5, math.exp(3.5), 50, math.exp(22/5), 96, math.exp(93/20),
                  3259 / 25, 16277 / 100,
                  290, root, 500, 800, 22221, Lmax]
    # Include both sides of each entrance so that jumps are drawn vertically.
    L = np.unique(np.concatenate([
        np.exp(np.linspace(math.log(math.log(3)), math.log(Lmax), 7000)),
        np.array(boundaries),
        np.nextafter(np.array(boundaries[1:-1]), -np.inf),
    ]))
    U = upper(L)
    # Direct candidate minimum independently checks the table regimes.
    direct = np.array([
        np.where(L < math.log(10), 5.0, L**2),
        np.where(L >= math.log(2984), (L - .001)**2, np.inf),
        np.where(L >= math.log(3295), (L - .1)**2, np.inf),
        np.where(L >= 12.5, (L - .5)**2, np.inf),
        np.where(L >= 16, (L - np.log(L) + 3)**2, np.inf),
        np.where(L >= 96, (L - np.log(L) + 11 / 4)**2, np.inf),
        np.where(L >= 50, (L - 2 * np.log(L) + 37 / 5)**2, np.inf),
        np.where(L >= 255, .9999 * L**2, np.inf),
        np.where(L >= 290, .99 * L**2, np.inf),
        np.where(L >= 500, (99 / 40) * ((500 / 821) * (L + 7 / 5) + 213 / 20)**2, np.inf),
        np.where(L >= 22221, .8 * L**2, np.inf),
        np.where((L >= 3259 / 25) & (L <= 16277 / 100),
                 ((3200 / 3241) * (L - 18 / 25))**2, np.inf),
    ])
    np.testing.assert_allclose(U, np.min(direct, axis=0), rtol=2e-15)
    assert np.all(U > 0)
    assert np.all(U[L >= math.log(10)] <= L[L >= math.log(10)]**2 * (1 + 1e-14))
    assert abs((root - 2 * math.log(root) + 37 / 5)**2 -
               (99 / 40) * ((500 / 821) * (root + 7 / 5) + 213 / 20)**2) < 1e-6

    data = DATA_DIR / "non_one_records.csv"
    with data.open(encoding="utf-8", newline="") as source:
        records = list(csv.DictReader(source))
    ns = [int(row["n"]) for row in records]
    qs = [int(row["witness"]) for row in records]
    assert len(records) == 49 and qs[-1] == 397
    assert all(a < b for a, b in zip(ns, ns[1:]))
    assert all(a < b for a, b in zip(qs, qs[1:]))
    actual_L = np.log(np.array(ns, dtype=float))
    assert np.all(np.array(qs) <= upper(actual_L))
    # This extension ends at the certified search limit; it is not extrapolated.
    actual_x = np.log(np.append(actual_L, 80 * math.log(2)))
    actual_y = np.array(qs + [qs[-1]])

    fig, ax = plt.subplots(figsize=(12, 8))
    fig.subplots_adjust(left=0.09, right=0.98, top=0.87, bottom=0.13)
    ax.plot(np.log(L), U, color="#d55e00", linewidth=2.5,
            label=r"GRH upper bound $U(n)$ (comparison table)", zorder=3)
    ax.plot(np.log(L), L**2, color="#333333", linewidth=1.7, linestyle=":",
            label=r"$(\ln n)^2$", zorder=4)
    ax.step(actual_x, actual_y, where="post", color="#007f80", linewidth=2,
            label=r"$Q_{\ne 1}(N)$: recorded values through $2^{80}$", zorder=5)
    ax.scatter(np.log(actual_L), qs, s=9, color="#007f80", zorder=6)
    ax.set_yscale("log")
    ax.set_xlim(math.log(math.log(3)), math.log(Lmax))
    ax.set_ylim(1, Lmax**2 * 1.2)
    powers = [2**k for k in range(15) if 2**k < args.max_power]
    powers.append(args.max_power)
    power_ticks(ax, powers)
    ax.set_xlabel(r"Odd nonsquare integer $n$ / upper bound $N$", labelpad=10)
    ax.set_ylabel("Least odd-prime witness / upper bound")
    ax.grid(which="major", color="#d8dde3", linewidth=0.7)
    bit_powers = [64, 80, 128]
    bit_positions = [math.log(k * math.log(2)) for k in bit_powers]
    for x in bit_positions:
        ax.axvline(x, color="#7e91ac", linestyle="--", linewidth=0.9, zorder=1)
    top = ax.secondary_xaxis("top")
    top.set_xticks(bit_positions, [rf"$2^{{{k}}}$" for k in bit_powers])
    top.tick_params(axis="x", colors="#536780", labelsize=10, pad=5)
    ax.legend(loc="upper left", framealpha=0.97, fontsize=10)
    ax.set_title(r"Non-one witnesses: $Q_{\ne 1}(N)$ and GRH upper bounds", pad=46)

    # The main curves nearly coincide on a logarithmic axis. An inset shows
    # their ratio, also on a logarithmic vertical axis, without changing the main scale.
    inset = ax.inset_axes([0.045, 0.53, 0.45, 0.28])
    keep = L >= math.log(10)
    inset.plot(np.log(L[keep]), U[keep] / L[keep]**2, color="#d55e00", linewidth=2)
    inset.axhline(1, color="#333333", linestyle=":", linewidth=1.3)
    inset.set_yscale("log")
    inset.set_xlim(math.log(math.log(10)), math.log(Lmax))
    inset.set_ylim(0.78, 1.006)
    inset.yaxis.set_major_locator(FixedLocator([0.8, 0.85, 0.9, 0.95, 1]))
    inset.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.2f}"))
    inset.yaxis.set_minor_locator(NullLocator())
    power_ticks(inset, [1, 4, 16, 64, 256, 1024, 4096, 16384])
    inset.tick_params(labelsize=9)
    inset.set_title(r"Detail: $U(n)/(\ln n)^2$", fontsize=10)
    inset.grid(color="#e1e5e9", linewidth=0.6)
    for x in bit_positions:
        inset.axvline(x, color="#7e91ac", linestyle="--", linewidth=0.8, zorder=1)
    inset.set_facecolor("#fafbfd")
    stem = args.output_dir / "qne1_upper_bound_comparison"
    fig.savefig(stem.with_suffix(".svg"), metadata={"Date": None})
    svg = stem.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text(encoding="utf-8").splitlines())
                   + "\n", encoding="utf-8")
    fig.savefig(stem.with_suffix(".png"), dpi=180)
    plt.close(fig)
    print(f"Wrote {stem}.svg and .png")
    print(f"Double-logarithm / two-pole crossing: ln B = {root:.12f}; "
          f"log10 B = {root / math.log(10):.12f}")
    print(f"Checked {len(L)} curve samples against 12 candidates, 49 recorded maxima, "
          "and the crossover residual.")


if __name__ == "__main__":
    main()
