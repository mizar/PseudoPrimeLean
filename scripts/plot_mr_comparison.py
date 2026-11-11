#!/usr/bin/env python3
"""Draw the current Miller-Rabin pointwise and cumulative witness bounds.

The pointwise branches are the certified small-input bounds, the global 3/11
bound, and the piecewise cutoff of refined_piecewise_witness. Cumulative
histories retain each branch's preceding entrance bound. All coordinates are
computed from L = ln(n); plotting is numerical, not a Lean proof. The
quarter-square curve through L = 465 uses the proved least-witness theorem.
The three-elevenths bound is Lean-proved for all odd composites under GRH.
"""

from __future__ import annotations

import argparse
import csv
import math
from pathlib import Path

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator

from plot_qne1_comparison import DATA_DIR, ROOT, power_ticks


ENTRANCES = ((1000.0, 3.0), (3000.0, 1.0), (10000.0, 0.0))
QUARTER_LOW = 200.0
QUARTER_HIGH = (200.0, 465.0)


def quarter_interval(L: np.ndarray) -> np.ndarray:
    """Identify the two proved pointwise quarter-bound intervals."""
    return (L <= QUARTER_LOW) | ((QUARTER_HIGH[0] <= L) & (L <= QUARTER_HIGH[1]))


def first_crossover() -> float:
    """Solve paper_bound(L, 3) = (3/11) L² on the first paper branch."""
    d, a, v = 24439 / 50000, 3 / (8 * (27 / 25)**5), 53 / 500
    q = 3 / 11
    slope = d * math.sqrt(q) - a
    root = (v * q**.25 + math.sqrt(v*v * math.sqrt(q) + 12 * slope)) / (2 * slope)
    return root**2


def paper_bound(L: np.ndarray, allowance: float | np.ndarray) -> np.ndarray:
    """Fourth power of the positive root in RefinedSixPolePaperRoot.lean."""
    d, a, v = 24439 / 50000, 3 / (8 * (27 / 25)**5), 53 / 500
    return ((v + np.sqrt(v*v + 4*d*(a*L + allowance))) / (2*d))**4


def paper_piecewise_upper(L: np.ndarray) -> np.ndarray:
    """Piecewise witness cutoff, certified for odd composites with L >= 8."""
    allowance = np.where(L < 3000, 3.0, np.where(L < 10000, 1.0, 0.0))
    return np.where(L < 1000, .3 * L**2, paper_bound(L, allowance))


def pointwise_upper(L: np.ndarray) -> np.ndarray:
    """Combine the small-input, 3/11 and piecewise witness cutoffs."""
    current = np.where(L < math.log(2047), 2.0,
                       np.where(L < math.log(3000), 3.0,
                                np.minimum(np.where(quarter_interval(L), .25, 3 / 11) * L**2,
                                           paper_piecewise_upper(L))))
    return np.minimum(current, np.maximum(2.0, (3 / 11) * L**2))


def cumulative_upper(L: np.ndarray) -> np.ndarray:
    """Cumulative bound on L >= ln(3000), retaining each entrance history."""
    result = np.maximum(2.0, np.where(L <= QUARTER_LOW, .25, 3 / 11) * L**2)
    high_quarter = np.maximum(.25 * QUARTER_HIGH[0]**2, .25 * L**2)
    result = np.where((QUARTER_HIGH[0] <= L) & (L <= QUARTER_HIGH[1]),
                      np.minimum(result, high_quarter), result)
    caps: list[float] = []
    for index, (entrance, allowance) in enumerate(ENTRANCES):
        anchor = max(2.0, (3 / 11) * entrance**2)
        for previous, (previous_entrance, previous_allowance) in enumerate(ENTRANCES[:index]):
            if entrance >= previous_entrance:
                old_branch = float(paper_bound(np.array([entrance]), previous_allowance)[0])
                anchor = min(anchor, max(caps[previous], old_branch))
        caps.append(anchor)
        result = np.where(L >= entrance,
                          np.minimum(result, np.maximum(anchor, paper_bound(L, allowance))),
                          result)
    return result


def load_records() -> tuple[list[int], list[int]]:
    """Load and independently check each recorded least rejecting prime."""
    with (DATA_DIR / "mr_records.csv").open(encoding="utf-8", newline="") as stream:
        records = list(csv.DictReader(stream))
    ns = [int(row["n"]) for row in records]
    ps = [int(row["witness"]) for row in records]
    assert len(records) == 11 and ps[-1] == 43
    assert all(a < b for a, b in zip(ns, ns[1:]))
    assert all(a < b for a, b in zip(ps, ps[1:]))
    assert np.all(np.asarray(ps) <= pointwise_upper(np.log(np.asarray(ns, dtype=float))))
    for n, p in zip(ns, ps):
        d, s = n - 1, 0
        while d % 2 == 0:
            d //= 2
            s += 1

        def passes(a: int) -> bool:
            value = pow(a, d, n)
            if value in (1, n - 1):
                return True
            for _ in range(1, s):
                value = value * value % n
                if value == n - 1:
                    return True
            return False

        primes = [a for a in range(2, p + 1)
                  if all(a % b for b in range(2, math.isqrt(a) + 1))]
        assert primes[-1] == p and not passes(p)
        assert all(passes(a) for a in primes[:-1])
    return ns, ps


def samples(lower: float, upper: float, count: int) -> np.ndarray:
    """Include both sides of every discontinuity inside the plotted interval."""
    switches = np.array([math.log(2047), math.log(3000), QUARTER_LOW, *QUARTER_HIGH,
                         1000.0, first_crossover(),
                         3000.0, 10000.0])
    points = np.unique(np.concatenate((np.geomspace(lower, upper, count), switches,
                                      np.nextafter(switches, -np.inf),
                                      np.nextafter(switches, np.inf), [lower, upper])))
    return points[(lower <= points) & (points <= upper)]


def save_figure(fig: plt.Figure, stem: Path) -> None:
    fig.savefig(stem.with_suffix(".svg"), metadata={"Date": None})
    svg = stem.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text(encoding="utf-8").splitlines())
                   + "\n", encoding="utf-8")
    fig.savefig(stem.with_suffix(".png"), dpi=180)
    plt.close(fig)


def plot_cumulative(output_dir: Path) -> None:
    L = samples(math.log(3000), 1e15, 6000)
    cumulative, pointwise = cumulative_upper(L), pointwise_upper(L)
    assert np.all(cumulative >= pointwise - 1e-12 * np.maximum(1, pointwise))
    assert np.all(np.diff(cumulative) >= -1e-13 * cumulative[1:])
    for threshold, _ in ENTRANCES:
        near = np.array([np.nextafter(threshold, -np.inf), threshold,
                         np.nextafter(threshold, np.inf)])
        assert pointwise_upper(near)[1] <= pointwise_upper(near)[0] * (1 + 1e-14)
        assert np.all(np.diff(cumulative_upper(near)) >= -1e-7)
    fig, ax = plt.subplots(figsize=(10, 5.5))
    ax.semilogx(L, cumulative / L**2, color="#d55e00", linewidth=2.5,
                label="Cumulative bound with piecewise cutoff")
    ax.semilogx(L, pointwise / L**2, color="#3977a8", linestyle="--",
                label="Pointwise bound with piecewise cutoff")
    ax.plot(L, np.maximum(2.0, (3 / 11) * L**2) / L**2, color="#333333", linestyle=":",
            linewidth=1.7, label=r"Lean theorem: $\max\{2,\frac{3}{11}(\ln N)^2\}$")
    quarter = L <= QUARTER_HIGH[1]
    ax.semilogx(L[quarter], np.maximum(2.0, .25 * L[quarter]**2) / L[quarter]**2,
                color="#8d48a3", linestyle="-.", linewidth=1.7, zorder=5,
                label=r"Lean theorem: $\max\{2,\frac{1}{4}L^2\}$, $L\leq465$")
    ax.set(xlabel=r"$L=\ln N$", ylabel=r"Upper bound divided by $L^2$",
           title="Cumulative bounds at high scales")
    ax.set_xlim(math.log(3000), 1e15)
    ax.grid(color="#e1e5e9", linewidth=.6)
    ax.legend(loc="upper right", fontsize=8)
    fig.tight_layout()
    save_figure(fig, output_dir / "mr_cumulative_high_comparison")


def plot_pointwise(output_dir: Path, max_power: int) -> None:
    ns, ps = load_records()
    record_L = np.log(np.asarray(ns, dtype=float))
    Lmax = max_power * math.log(10)
    L = samples(math.log(9), Lmax, 10000)
    upper = pointwise_upper(L)
    fig, ax = plt.subplots(figsize=(12, 8))
    fig.subplots_adjust(left=.09, right=.95, top=.87, bottom=.13)
    ax.plot(np.log(L), upper, color="#d55e00", linewidth=2.5,
            label=r"Pointwise bound $U_{\mathrm{new}}(n)$", zorder=3)
    ax.plot(np.log(L), np.maximum(2.0, (3 / 11) * L**2), color="#333333", linewidth=1.7,
            linestyle=":", label=r"Lean theorem: $\max\{2,\frac{3}{11}(\ln n)^2\}$", zorder=4)
    for i, quarter in enumerate((L <= QUARTER_LOW,
                                 (QUARTER_HIGH[0] <= L) & (L <= QUARTER_HIGH[1]))):
        ax.plot(np.log(L[quarter]), np.maximum(2.0, .25 * L[quarter]**2),
                color="#8d48a3", linestyle="-.", linewidth=1.7, zorder=5,
                label=r"Lean theorem: $\max\{2,\frac{1}{4}L^2\}$, $L=\ln n\leq465$"
                if i == 0 else None)
    ax.step(np.log(record_L), ps, where="post", color="#007f80", linewidth=2, zorder=5)
    ax.scatter(np.log(record_L), ps, s=27, color="#007f80", zorder=7,
               label=r"Record points $Q_{\mathrm{MR}}(N)$ (OEIS A006945; prime bases 2, 3, 5, …)")
    ax.set_yscale("log")
    ax.set_xlim(math.log(math.log(9)), math.log(Lmax))
    ax.set_ylim(1, max(1e4, 1.1 * float(np.max(upper))))
    powers = [2**k for k in range(14) if 2**k < max_power] + [max_power]
    power_ticks(ax, powers)
    ax.set_xlabel(r"Odd composite integer $n$ / upper bound $N$", labelpad=10)
    ax.set_ylabel("Least prime witness / upper bound")
    ax.grid(which="major", color="#d8dde3", linewidth=.7)
    bits = [k for k in [64, 80, 128] if k * math.log(2) <= Lmax]
    positions = [math.log(k * math.log(2)) for k in bits]
    for position in positions:
        ax.axvline(position, color="#7e91ac", linestyle="--", linewidth=.9, zorder=1)
    top = ax.secondary_xaxis("top")
    top.set_xticks(positions, [rf"$2^{{{k}}}$" for k in bits])
    top.tick_params(axis="x", colors="#536780", labelsize=10, pad=5)
    ax.legend(loc="upper left", framealpha=.97, fontsize=10)
    ax.set_title("Miller–Rabin: least-prime witness bounds", pad=46)
    inset = ax.inset_axes([.06, .44, .32, .28])
    inset_L = samples(math.log(3000), 1e14, 10000)
    inset.plot(np.log(inset_L), pointwise_upper(inset_L) / inset_L**2,
               color="#d55e00", linewidth=2)
    inset.axhline(3 / 11, color="#333333", linestyle=":", linewidth=1.3)
    inset.set_yscale("log")
    inset.set_xlim(math.log(math.log(3000)), math.log(1e14))
    inset.set_ylim(.247, .276)
    inset.yaxis.set_major_locator(FixedLocator([.25, .26, .27, 3 / 11]))
    inset.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.4f}"))
    inset.yaxis.set_minor_locator(NullLocator())
    ticks = [(math.log(k * math.log(10)), rf"$10^{{{k}}}$") for k in (4, 64)]
    ticks += [(k * math.log(10), rf"$e^{{10^{{{k}}}}}$") for k in (4, 6, 8, 10, 12, 14)]
    ticks.sort()
    inset.xaxis.set_major_locator(FixedLocator([position for position, _ in ticks]))
    inset.xaxis.set_major_formatter(FuncFormatter(
        lambda x, _: next((label for position, label in ticks if np.isclose(x, position)), "")))
    inset.xaxis.set_minor_locator(NullLocator())
    inset.tick_params(labelsize=9)
    inset.set_title(r"Detail: $U_{\mathrm{new}}(n)/(\ln n)^2$", fontsize=10)
    inset.grid(color="#e1e5e9", linewidth=.6)
    for position in [math.log(k * math.log(2)) for k in [64, 80, 128]]:
        inset.axvline(position, color="#7e91ac", linestyle="--", linewidth=.8, zorder=1)
    inset.set_facecolor("#fafbfd")
    save_figure(fig, output_dir / "mr_upper_bound_comparison")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "doc/figures")
    parser.add_argument("--max-power", type=int, default=256)
    args = parser.parse_args()
    if not 1 <= args.max_power <= 8192:
        parser.error("--max-power must be between 1 and 8192")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 11, "svg.hashsalt": "mr-comparison",
                         "axes.spines.top": False, "axes.spines.right": False})
    plot_pointwise(args.output_dir, args.max_power)
    plot_cumulative(args.output_dir)
    print(f"Wrote Miller-Rabin comparison figures to {args.output_dir}")


if __name__ == "__main__":
    main()
