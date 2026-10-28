#!/usr/bin/env python3
"""Plot the QNegOne comparison in doc/PseudoSquare.md using Matplotlib.

Run with matplotlib installed. Horizontal positions are ln(ln B), labelled
as powers of ten; vertical values use a logarithmic axis. Calculations use
L = ln B so the enormous endpoints never need to be constructed.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
from pathlib import Path

from plot_qne1_comparison import DATA_DIR, ROOT, power_ticks
import matplotlib.pyplot as plt
import numpy as np
from matplotlib.ticker import FixedLocator, FuncFormatter, NullLocator


ENTRANCE = 255


def elementary_radius(L: np.ndarray) -> np.ndarray:
    """R(B), evaluated at L = ln B."""
    log4B = L + math.log(4)
    return (log4B + 4.8 * np.log(log4B) + 3)**2


def upper(L: np.ndarray) -> np.ndarray:
    """The five regimes of the published QNegOne comparison table."""
    baseline = np.select([L < ENTRANCE, L < 290, L < 600, L < 19978 * math.log(10)],
                     [elementary_radius(L), 0.9999 * L**2, 0.99 * L**2,
                      (99 / 40) * ((500 / 821) * (L + 7 / 5) +
                                  (11 / 10) * np.log(L + 7 / 5) + 6)**2],
                     default=0.8 * L**2)
    return np.minimum(baseline,np.where(L >= 500,
        (99 / 40) * ((500 / 821) * (L + 7 / 5) +
                      (11 / 10) * np.log(L + 7 / 5) + 6)**2,np.inf))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "doc/figures")
    parser.add_argument("--max-power", type=int, default=32768,
                        help="Right endpoint B = 10**max_power (default: 32768).")
    parser.add_argument("--negative-minima", type=Path,
                        default=DATA_DIR / "negative_prime_minima.csv",
                        help="Prime-wise least inputs used to extract maximum-update points.")
    args = parser.parse_args()
    if args.max_power < 128:
        parser.error("--max-power must be at least 128 to include both entrances")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 11, "svg.hashsalt": "qneg1-comparison",
                         "axes.spines.top": False, "axes.spines.right": False})

    Lmax = args.max_power * math.log(10)
    entrances = np.array([ENTRANCE, 290.0, 500.0, 550.0, 600.0, 19978 * math.log(10)])
    L = np.unique(np.concatenate([
        np.exp(np.linspace(math.log(math.log(3)), math.log(Lmax), 7000)),
        [math.log(3), 200.0, Lmax], entrances,
        np.nextafter(entrances, -np.inf),
    ]))
    U = upper(L)
    assert np.all(U > 0)
    assert np.all(U[L < ENTRANCE] > L[L < ENTRANCE]**2)
    assert np.all(U[L >= ENTRANCE] < L[L >= ENTRANCE]**2)
    assert np.isclose(upper(np.array([ENTRANCE]))[0], 0.9999 * ENTRANCE**2)
    assert np.isclose(upper(np.array([290.0]))[0], 0.99 * 290**2)

    candidates = np.stack([
        elementary_radius(L),
        np.where(L >= ENTRANCE, 0.9999 * L**2, np.inf),
        np.where(L >= 290, 0.99 * L**2, np.inf),
        np.where(L >= 500, (99 / 40) * ((500 / 821) * (L + 7 / 5) +
                                  (11 / 10) * np.log(L + 7 / 5) + 6)**2, np.inf),
        np.where(L >= 19978 * math.log(10), 0.8 * L**2, np.inf),
    ])
    assert np.allclose(U, np.min(candidates, axis=0), rtol=1e-12, atol=0)
    assert upper(np.array([600.0]))[0] < .99 * 600**2

    data_dir = DATA_DIR
    with (data_dir / "negative_records.csv").open(encoding="utf-8", newline="") as f:
        records = list(csv.DictReader(f))
    evidence = json.loads((data_dir / "negative_results.json").read_text(encoding="utf-8"))
    ns = [int(row["n"]) for row in records]
    qs = [int(row["witness"]) for row in records]
    assert evidence["complete"]
    assert evidence["upper_exclusive"] == 2**72
    assert list(zip(ns, qs)) == [(r["n"], r["witness"]) for r in evidence["records"]]
    assert len(records) == 32 and qs[-1] == 383
    assert all(a < b for a, b in zip(ns, ns[1:]))
    assert all(a < b for a, b in zip(qs, qs[1:]))
    with args.negative_minima.open(encoding="utf-8-sig", newline="") as f:
        minima = {int(row["witness"]): int(row["n"]) for row in csv.DictReader(f) if row["n"]}
    assert all(minima[p] == n for n, p in zip(ns, qs))
    primes = [p for p in range(3, max(minima) + 1, 2)
              if all(p % d for d in range(3, math.isqrt(p) + 1, 2))]
    for p, n in minima.items():
        assert p in primes and n > 1 and n % 2 and math.isqrt(n)**2 != n
        assert all(pow(n % q, (q - 1) // 2, q) != q - 1 for q in primes if q < p)
        assert pow(n % p, (p - 1) // 2, p) == p - 1
    # Plot only cumulative-maximum updates in the independently audited range.
    # Other prime-wise first occurrences do not belong on this figure.
    derived = []
    maximum = 0
    for n, p in sorted((n, p) for p, n in minima.items() if n < 2**64):
        if p > maximum:
            derived.append((n, p))
            maximum = p
    assert derived == [(n, p) for n, p in zip(ns, qs) if n < 2**64]
    # Complete the record sequence using the verified 2**72 search snapshot.
    endpoint383 = 1736820352691539357719
    assert minima[349] == 451368766434936754915
    assert minima[383] == endpoint383
    assert all(p not in minima or minima[p] >= evidence["upper_exclusive"]
               for p in [353, 359, 367, 373, 379])
    assert endpoint383 < 1900000000000000000000
    derived.extend([(minima[349], 349), (endpoint383, 383)])
    assert derived == list(zip(ns, qs))
    ns = [n for n, p in derived]
    qs = [p for n, p in derived]
    actual_L = np.log(np.array(ns, dtype=float))
    assert np.all(np.array(qs) <= upper(actual_L))
    # 2**64 is even, so the odd-input maximum there equals the maximum below it.
    actual_x = np.log(actual_L)
    actual_y = np.array(qs)

    fig, ax = plt.subplots(figsize=(12, 8))
    fig.subplots_adjust(left=0.115, right=0.97, top=0.87, bottom=0.19)
    ax.plot(np.log(L), U, color="#d55e00", linewidth=2.5,
            label=r"GRH upper bound $U_{-1}(n)$ (comparison table)", zorder=3)
    ax.plot(np.log(L), L**2, color="#333333", linewidth=1.7, linestyle=":",
            label=r"$(\ln n)^2$", zorder=4)
    ax.step(actual_x, actual_y, where="post", color="#007f80", linewidth=2,
            label=r"$Q_{-1}(N)$: records through $q_{-1}=383$", zorder=5)
    ax.scatter(np.log(actual_L), qs, s=9, color="#007f80", zorder=6)
    ax.set_yscale("log")
    ax.set_xlim(math.log(math.log(3)), math.log(Lmax))
    ax.set_ylim(1, Lmax**2 * 1.2)
    powers = sorted({k for k in [2**j for j in range(16)] if k < args.max_power}
                    | {args.max_power})
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
    ax.set_title(r"Negative witnesses: $Q_{-1}(N)$ and GRH upper bounds", pad=46)

    # Zoom into the analytic entrances; keep the inset vertical scale logarithmic.
    inset = ax.inset_axes([0.045, 0.50, 0.36, 0.23])
    keep = L >= 200
    inset.plot(np.log(L[keep]), U[keep] / L[keep]**2, color="#d55e00", linewidth=2)
    inset.axhline(1, color="#333333", linestyle=":", linewidth=1.3)
    inset.set_yscale("log")
    inset.set_xlim(math.log(80), math.log(Lmax))
    inset.set_ylim(0.78, 1.38)
    inset.yaxis.set_major_locator(FixedLocator([.8, .9, 1, 1.1, 1.2, 1.3]))
    inset.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.2f}"))
    inset.yaxis.set_minor_locator(NullLocator())
    power_ticks(inset, [128, 512, 2048, 8192, 32768])
    inset.tick_params(labelsize=9)
    inset.set_title(r"Detail: $U_{-1}(n)/(\ln n)^2$", fontsize=10)
    inset.grid(color="#e1e5e9", linewidth=0.6)
    inset.set_facecolor("#fafbfd")
    stem = args.output_dir / "qneg1_upper_bound_comparison"
    fig.savefig(stem.with_suffix(".svg"), metadata={"Date": None})
    svg = stem.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text(encoding="utf-8").splitlines())
                   + "\n", encoding="utf-8")
    fig.savefig(stem.with_suffix(".png"), dpi=180)
    plt.close(fig)
    print(f"Wrote {stem}.svg and .png")
    print(f"Checked {len(L)} samples against five candidates, 32 recorded maxima, "
          "and all entrance endpoints.")
    print(f"Verified {len(minima)} prime-wise negative minima and extracted only {len(derived)} record points "
          f"from {args.negative_minima}.")


if __name__ == "__main__":
    main()
