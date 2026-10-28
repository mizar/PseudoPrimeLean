#!/usr/bin/env python3
"""Plot the pointwise Miller-Rabin witness-bound comparison in the public docs.

Install matplotlib, then run this script. By default, the plot covers
9 <= n <= 10**1024. Set --max-power to extend it, up to 10**8192.
Coordinates use L = ln n, never n.
Record points are pointwise witnesses, not an extrapolated finite-maximum bound.
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


def adaptive_root(L: np.ndarray) -> np.ndarray:
    t = L - 2 * np.log(L) + 45571 / 10000
    return (L - 2 * np.log(L) + 113911 / 25000
            + 231 / (2500 * (t - 1)) - 16033 / (4500 * t**2))


def gaussian_6fifths_bound(L: np.ndarray) -> np.ndarray:
    mass = 16 / 25
    endpoint = 2129 / 2000
    index = 1000000000
    conductor = 161 / 400
    d = (index * mass - endpoint) / (index - 1)
    beta = (index / (index - 1)) * (mass / 3 + 3 / 10)
    root = (beta + np.sqrt(beta**2 + 4 * d * (conductor * L + 29))) / (2 * d)
    return (6 / 5) * root**4


def gamma_clipped_prefix_root(L: np.ndarray, credit: float) -> np.ndarray:
    offset = 143420077 / 11856000 - 2 * credit
    linear = (11783423 / 25000000) * L + offset
    reciprocal = (7 / 6) * L + 190 / 3
    return (linear + np.sqrt(linear**2 + 4 * (87069 / 98800) * reciprocal)) \
        / (2 * (87069 / 98800))


def gamma_clipped_upper(L: np.ndarray) -> np.ndarray:
    first = np.maximum(1000, (99 / 40) * gamma_clipped_prefix_root(L, 203 / 50)**2)
    second = np.maximum(50000, (99 / 40) * gamma_clipped_prefix_root(L, 28493 / 5000)**2)
    return np.minimum(first, second)


def gamma_midscale_upper(L: np.ndarray) -> np.ndarray:
    """The certified 35000 prefix and the refined 1000 prefix, valid for L >= 120."""
    first = np.maximum(35000, (99 / 40) * gamma_clipped_prefix_root(L, 11147 / 2000)**2)
    second = np.maximum(1000, (99 / 40) * gamma_clipped_prefix_root(L, 413 / 100)**2)
    return np.minimum(first, second)


def endpoint_midscale_base(L: np.ndarray) -> np.ndarray:
    """The 7/4 endpoint ranges before adding the two-step candidate."""
    return np.select(
        [L <= 22, L <= 111 / 4, L <= 144 / 5],
        [(64 / 81) * (L - 7 / 4)**2, (81 / 100) * (L - 7 / 4)**2,
         np.full_like(L, 576)],
        default=midscale_root(L - 7 / 4)**2,
    )


def gamma_index100_bound(L: np.ndarray) -> np.ndarray:
    mu = 11783423 / 25000000
    a = 91 / 100
    linear = mu * L + 1057 / 2500
    reciprocal = (7 / 6) * L + 61
    radius = (linear + np.sqrt(linear**2 + 4 * a * reciprocal)) / (2 * a)
    return (99 / 40) * radius**2


def gamma_index100_prefix_upper(L: np.ndarray) -> np.ndarray:
    """Minimum of the retained 1000-term and 50000-term Gamma prefixes."""
    mu = 11783423 / 25000000

    def prefix_bound(credit: float, floor: float) -> np.ndarray:
        linear = mu * L + (591 / 50 - 2 * credit)
        reciprocal = (7 / 6) * L + 61
        radius = (linear + np.sqrt(linear**2 + 4 * (91 / 100) * reciprocal)) \
            / (2 * (91 / 100))
        return np.maximum(floor, (99 / 40) * radius**2)

    return np.minimum(prefix_bound(203 / 50, 1000),
                      prefix_bound(28493 / 5000, 50000))


def gaussian_18_bound(L: np.ndarray) -> np.ndarray:
    """Analysis13's constant-18 version of the 6/5 Gaussian bound."""
    mass = 16 / 25
    endpoint = 2129 / 2000
    index = 1000000000
    conductor = 161 / 400
    d = (index * mass - endpoint) / (index - 1)
    beta = (index / (index - 1)) * (mass / 3 + 3 / 10)
    root = (beta + np.sqrt(beta**2 + 4 * d * (conductor * L + 18))) / (2 * d)
    return (6 / 5) * root**4


def gaussian_6_bound(L: np.ndarray) -> np.ndarray:
    """The unchanged constant-6 Gaussian bound, now valid from scale 240."""
    mass = 16 / 25
    endpoint = 2129 / 2000
    index = 1000000000
    conductor = 161 / 400
    d = (index * mass - endpoint) / (index - 1)
    beta = (index / (index - 1)) * (mass / 3 + 3 / 10)
    root = (beta + np.sqrt(beta**2 + 4 * d * (conductor * L + 6))) / (2 * d)
    return (6 / 5) * root**4


def gaussian_refined_bound(L: np.ndarray) -> np.ndarray:
    """Separate refined Gaussian bound, proved for logarithmic scale at least 300."""
    mass = 64167 / 100000
    endpoint = 2129 / 2000
    index = 1000000000
    conductor = 20115621 / 50000000
    width = 2 / 5
    d = (index * mass - endpoint) / (index - 1)
    beta = (index / (index - 1)) * (width * mass + 1 / (10 * width))
    root = (beta + np.sqrt(beta**2 + 4 * d * (conductor * L + 28 / 5))) / (2 * d)
    return (6 / 5) * root**4


def midscale_root(L: np.ndarray) -> np.ndarray:
    return np.select([L <= 703 / 20, L <= 10367 / 200, L <= 1706 / 25,
                      L <= 6671 / 50],
                     [(800 / 837) * (L - 167 / 100),
                      (3200 / 3337) * (L - 89 / 50),
                      (3200 / 3281) * (L - 131 / 50),
                      (3200 / 3259) * (L - 153 / 50)],
                     default=(12800 / 12927) * (L - 83 / 20))


def even_two_step_cutoff(L: np.ndarray) -> np.ndarray:
    """Two fixed substitutions in the normalized even endpoint correction."""
    def correction(y: np.ndarray) -> np.ndarray:
        z = np.log(y)
        numerator = (
            36620000 * y**3 * z - 56749471 * y**3
            + 109860000 * y**2 * z**2 + 73100099 * y**2 * z
            + 10777809 * y**2 - 73240000 * y * z**2
            - 1528140 * y * z + 2824690 * y - 36620000 * z**2
            - 177204180 * z - 94877470
        )
        denominator = 18310000 * (y - 1) * ((y + 1)**2 + 2 * y * z)
        return numerator / denominator

    first = np.maximum(8, L - correction(L))
    second = L - correction(first)
    return second**2


def shift117_minus_two_crossing() -> float:
    return (47366 + math.sqrt(47366**2 + 4 * 2723311)) / 2


def shifted_endpoint_w1000_crossing(shift: float = 9 / 8) -> float:
    a0 = 12800 / 12927
    s0 = math.sqrt(99 / 40)
    return (9 * s0 + (shift + 83 / 20) * a0) / (a0 - (287 / 500) * s0)


def compatible_candidates(L: np.ndarray) -> np.ndarray:
    """All-input bounds checked against the documented envelope."""
    return np.array([
        np.where(L < math.log(2047), 2.0, np.inf),
        np.where((L >= math.log(2047)) & (L < math.log(3000)), 3.0, np.inf),
        np.where((L >= math.log(3000)) & (L <= 9), 61.0, np.inf),
        np.where((L >= math.log(3000)) & (L <= 56 / 5), 61.0, np.inf),
        np.where(L >= math.log(600), adaptive_root(L)**2, np.inf),
        np.where((L > 9) & (L < 81 / 8), (64 / 81) * L**2, np.inf),
        np.where((L >= 81 / 8) & (L <= 171 / 8),
                 (64 / 81) * (L - 9 / 8)**2, np.inf),
        np.where((L > 171 / 8) & (L <= 217 / 8),
                 (81 / 100) * (L - 9 / 8)**2, np.inf),
        np.where((L > 217 / 8) & (L <= 5581 / 200), 576.0, np.inf),
        np.where((L > 5581 / 200) & (L < shifted_endpoint_w1000_crossing()),
                 midscale_root(L - 9 / 8)**2, np.inf),
        np.where((L >= 523 / 50) & (L <= 2171 / 100),
                 (64 / 81) * (L - 73 / 50)**2, np.inf),
        np.where((L >= 23 / 2) & (L <= 240), even_two_step_cutoff(L), np.inf),
        np.where((L >= math.log(3000)) & (L <= 286 / 25), 61.0, np.inf),
        np.where((L >= 43 / 4) & (L <= 22), (64 / 81) * (L - 7 / 4)**2, np.inf),
        np.where((L >= 43 / 4) & (L <= 111 / 4), (81 / 100) * (L - 7 / 4)**2, np.inf),
        np.where(L >= 120, gamma_midscale_upper(L), np.inf),
        np.where((L >= 63) & (L <= 240), 35000.0, np.inf),
        np.where(L >= 240, gamma_index100_prefix_upper(L), np.inf),
        np.where(L >= 300, gaussian_18_bound(L), np.inf),
        np.where(L >= 240, gaussian_6_bound(L), np.inf),
        np.where(L >= 300, gaussian_refined_bound(L), np.inf),
        np.where((L >= 523 / 50) & (L <= 1373 / 50),
                 (81 / 100) * (L - 73 / 50)**2, np.inf),
        np.where((L >= 2171 / 100) & (L <= 144 / 5), 576.0, np.inf),
        np.where((L >= 706 / 25) & (L <= 5283 / 20),
                 midscale_root(L - 73 / 50)**2, np.inf),
        np.where((L >= 144 / 5) & (L <= 13517 / 100),
                 midscale_root(L - 7 / 4)**2, np.inf),
        np.where(L >= 300, (99 / 40) * ((500 / 821) * L + 3)**2, np.inf),
        np.where(L >= 11255, 0.8 * L**2, np.inf),
        np.where((L >= 1339 / 50) & (L <= 26269 / 100), midscale_root(L)**2, np.inf),
        np.where(L >= math.log(3000), (199 / 250) * (L + 216)**2, np.inf),
        np.where(L >= 210, (99 / 40) * ((287 / 500) * L + 9)**2, np.inf),
        np.where(L >= 240, (99 / 40) * ((287 / 500) * L + 9 / 2)**2, np.inf),
        np.where(L >= 258, (99 / 40) * ((107 / 200) * L + 24 / 5)**2, np.inf),
        np.where(L >= 4000,
                 (21 / 10) * ((5503 / 10000) * L + (4 / 5) * np.sqrt(L) + 46)**2,
                 np.inf),
        np.where(L >= 500, gaussian_6fifths_bound(L), np.inf),
        np.where(L >= 330, gamma_index100_bound(L), np.inf),
        np.where(L >= 34971, (4 / 5) * (L + 29)**2, np.inf),
        np.where(L >= 34971, (199 / 250) * (L + 117)**2, np.inf),
        np.where(L >= 46330, (4 / 5) * (L - 2)**2, np.inf),
        np.where(L >= 50880, (4 / 5) * (L - np.log(L))**2, np.inf),
        np.where(L >= 350000, (16 / 25) * L**2, np.inf),
        np.where(L >= 9565217391305 * math.log(10),
                 (282924 / 1000000) * L**2, np.inf),
        np.where((L >= 120) & (L < 500), gamma_clipped_upper(L), np.inf),
    ])


def previous_upper(L: np.ndarray) -> np.ndarray:
    """The retained high-range envelope and comparison baseline."""
    shifted_crossing = shifted_endpoint_w1000_crossing(73 / 50)
    endpoint_gamma = np.minimum(midscale_root(L - 7 / 4)**2, gamma_clipped_upper(L))
    previous = np.select(
        [L < math.log(2047), L < math.log(3000), L <= 56 / 5, L < 23 / 2,
         L <= 74 / 5, L <= 2171 / 100,
         L <= 1373 / 50, L <= 144 / 5, L < 120, L < 122, L < 330, L < 500,
         L < 9565217391305 * math.log(10),
         ],
        [np.full_like(L, 2), np.full_like(L, 3), np.full_like(L, 61),
         (64 / 81) * (L - 73 / 50)**2, even_two_step_cutoff(L),
         (64 / 81) * (L - 73 / 50)**2, (81 / 100) * (L - 73 / 50)**2,
         np.full_like(L, 576), midscale_root(L - 7 / 4)**2,
         endpoint_gamma, gamma_clipped_upper(L), gamma_index100_bound(L),
         gaussian_6fifths_bound(L)],
        default=(282924 / 1000000) * L**2,
    )
    return np.minimum.reduce([
        previous,
        np.where(L >= 240, gamma_index100_prefix_upper(L), np.inf),
        np.where(L >= 300, gaussian_18_bound(L), np.inf),
        np.where(L >= 240, gaussian_6_bound(L), np.inf),
        np.where(L >= 300, gaussian_refined_bound(L), np.inf),
    ])


def gamma_fixed_switch() -> float:
    """Numerical rendering of the exact Lean gammaFixedSwitch (208 < S < 209)."""
    radius = math.sqrt((40 / 99) * 35000)
    offset = 143420077 / 11856000 - 2 * (413 / 100)
    return ((87069 / 98800) * radius - offset - (190 / 3) / radius) / (
        11783423 / 25000000 + (7 / 6) / radius)


def compatible_upper(L: np.ndarray) -> np.ndarray:
    """Explicit Lean selectedWitnessEnvelope; continuous dominance is formally proved."""
    return np.select(
        [L < math.log(2047), L < math.log(3000), L <= 286 / 25,
         L < 23 / 2, L < 120, L <= gamma_fixed_switch(), L <= 240,
         L < 300, L < 9565217391305 * math.log(10)],
        [np.full_like(L, 2), np.full_like(L, 3), np.full_like(L, 61),
         (64 / 81) * (L - 7 / 4)**2, even_two_step_cutoff(L),
         np.maximum(1000, (99 / 40) * gamma_clipped_prefix_root(L, 413 / 100)**2),
         np.full_like(L, 35000), gaussian_6_bound(L), gaussian_refined_bound(L)],
        default=(282924 / 1000000) * L**2,
    )



def endpoint_correction(y: np.ndarray) -> np.ndarray:
    z = np.log(y)
    numerator = (36620000 * (3*y+1) * (y-1) * z**2
                 + (36620000*y**3 + 73100099*y**2 - 1528140*y - 177204180)*z
                 - 56749471*y**3 + 10777809*y**2 + 2824690*y - 94877470)
    return numerator / (18310000*(y-1)*((y+1)**2 + 2*y*z))


def even_four_step_cutoff(L: np.ndarray) -> np.ndarray:
    # Only L>=45/4 is a candidate; clamp inactive vector entries before logarithms.
    L = np.maximum(L, 45/4)
    a = np.maximum(8, L-endpoint_correction(L))
    b = L-endpoint_correction(a)
    c = np.maximum(8, L-endpoint_correction(b))
    return (L-endpoint_correction(c))**2


def gamma_sharp_bound(L: np.ndarray) -> np.ndarray:
    K, mu, D, T = 86733/98800, 11783423/25000000, 38128717/11856000, 20475759/494000
    v = mu*L+D
    r = (v+np.sqrt(v*v+4*K*(7*L/6+T)))/(2*K)
    return (99/40)*r*r


def gamma_sharp_switch() -> float:
    R = math.sqrt(1400000/99)
    return ((86733/98800)*R-38128717/11856000-(20475759/494000)/R) / (
        11783423/25000000+7/(6*R))


def gaussian_coefficients() -> tuple[float, float, float]:
    J, M, E, k = 1e9, 64167/100000, 2129/2000, 2/5
    return (J*M-E)/(J-1), (J/(J-1))*(k*M+1/(10*k)), 20115621/50000000


def gaussian_raw_bound(L: np.ndarray, D: float) -> np.ndarray:
    d, beta, c = gaussian_coefficients()
    t = (beta+np.sqrt(beta*beta+4*d*(c*L+D)))/(2*d)
    return (6/5)*t**4


def gaussian_switch(N: int, D: float) -> float:
    d, beta, c = gaussian_coefficients()
    r = math.sqrt(5*N/6)
    return (d*r-beta*math.sqrt(r)-D)/c


def gaussian_selected(L: np.ndarray) -> np.ndarray:
    s1, s2, s3 = (gaussian_switch(35000, 29/5), gaussian_switch(50000, 29/5),
                  gaussian_switch(50000, 111/20))
    return np.select([L <= s1, L < s2, L <= s3],
                     [np.full_like(L, 35000), gaussian_raw_bound(L, 29/5),
                      np.full_like(L, 50000)], default=gaussian_raw_bound(L, 111/20))


def previous_candidates(L: np.ndarray) -> np.ndarray:
    small = np.where(L < math.log(2047), 2., 3.)
    return np.array([
        compatible_upper(L),
        np.where(L < math.log(3000), small, np.inf),
        np.where(L <= 2877/250, 61., np.inf),
        np.where(L <= 47/4, 67., np.inf),
        np.where(L >= 45/4, even_four_step_cutoff(L), np.inf),
        np.where(L >= 100, gamma_sharp_bound(L), np.inf),
        np.where(L >= 63, np.maximum(35000, gaussian_raw_bound(L, 29/5)), np.inf),
        np.where(L >= 63, np.maximum(50000, gaussian_raw_bound(L, 111/20)), np.inf),
        np.where(L >= 2e12, (282924/1000000)*L**2, np.inf),
    ])


def previous_upper(L: np.ndarray) -> np.ndarray:
    """Numerical rendering of Lean improvedSelectedEnvelope and its exact switches."""
    four, gamma = even_four_step_cutoff(L), gamma_sharp_bound(L)
    small = np.where(L < math.log(2047), 2., 3.)
    return np.select(
        [L < math.log(3000), L <= 2877/250, L <= 47/4, L < 100, L < 112,
         L <= gamma_sharp_switch(), L <= 240, L < 2e12],
        [small, np.full_like(L, 61), np.full_like(L, 67), four, np.minimum(four, gamma),
         gamma, np.full_like(L, 35000), gaussian_selected(L)],
        default=(282924/1000000)*L**2)



LOW_PRIME_STEPS = [(23, 401/50), (29, 413/50), (31, 893/100), (37, 933/100),
                   (41, 238/25), (43, 989/100), (47, 521/50), (53, 109/10), (59, 553/50)]


def pointwise_cutoff(L: np.ndarray) -> np.ndarray:
    """Clipped inverse of y+H_pt(y), using the proved increasing domain y>=8."""
    lo = np.full_like(L, 8.)
    hi = np.maximum(8., L)
    for _ in range(64):
        y = (lo+hi)/2
        z = np.log(y)
        loss = 78861/50000 + 231/(5000*y) - 16033/(9000*y*y)
        delta = 2*y*y*(y+1+z)*(31551/20000-loss)/((y-1)*((y+1)**2+2*y*z))
        below = y+endpoint_correction(y)+delta < L
        lo = np.where(below, y, lo)
        hi = np.where(below, hi, y)
    return ((lo+hi)/2)**2


def gaussian1000_bound(L: np.ndarray) -> np.ndarray:
    d, beta, c = gaussian_coefficients()
    M, E, k = 64167/100000, 2129/2000, 2/5
    d4 = (4*M-E)/3
    beta4 = (4/3)*(M*k+1/(10*k))
    large = (beta+np.sqrt(beta*beta+4*d*(c*L+163/20)))/(2*d)
    four = (beta4+np.sqrt(beta4*beta4+4*d4*((2/3)*c*L+127/10)))/(2*d4)
    return (6/5)*np.maximum(10, np.maximum(large, four))**4


def gamma_reflected_bound(L: np.ndarray) -> np.ndarray:
    K, mu, D, T = 86733/98800, 11783423/25000000, 38128717/11856000, 58129633/2223000
    v = mu*L+D
    r = (v+np.sqrt(v*v+4*K*(7*L/6+T)))/(2*K)
    return (99/40)*r*r


def gaussian_seeded_selected(L: np.ndarray) -> np.ndarray:
    s1, s2, s3 = (gaussian_switch(35000, 567/100), gaussian_switch(50000, 567/100),
                  gaussian_switch(50000, 109/20))
    return np.select([L <= s1, L < s2, L <= s3],
                     [np.full_like(L, 35000), gaussian_raw_bound(L, 567/100),
                      np.full_like(L, 50000)], default=gaussian_raw_bound(L, 109/20))


def next_candidates(L: np.ndarray) -> np.ndarray:
    """The guarded baseline nextWitnessEnvelope, including all nine low-prime certificates."""
    result = [previous_upper(L), pointwise_cutoff(L),
              np.where(L >= 63, gaussian1000_bound(L), np.inf),
              np.where(L >= 100, gamma_reflected_bound(L), np.inf),
              np.where(L >= 63, np.maximum(35000, gaussian_raw_bound(L, 567/100)), np.inf),
              np.where(L >= 63, np.maximum(50000, gaussian_raw_bound(L, 109/20)), np.inf),
              np.where(L <= 11509/1000, 61., np.inf),
              np.where(L <= 1179/100, 67., np.inf),
              np.where(L <= 1193/100, 71., np.inf),
              np.where(L <= 12337/1000, 73., np.inf),
              np.where(L >= 1.5e12, (282924/1000000)*L**2, np.inf),
              np.where(L >= 2e12, (2827/10000)*L**2, np.inf)]
    result.extend(np.where(L <= cap, float(b), np.inf) for b, cap in LOW_PRIME_STEPS)
    return np.array(result)


def next_upper(L: np.ndarray) -> np.ndarray:
    """Baseline Lean nextSelectedEnvelope; numerical inverse evaluation is for rendering."""
    P, A, G = pointwise_cutoff(L), gaussian1000_bound(L), gamma_reflected_bound(L)
    low = np.select([L <= cap for _, cap in LOW_PRIME_STEPS],
                    [np.full_like(L, b) for b, _ in LOW_PRIME_STEPS], default=np.inf)
    small = np.where(L < math.log(2047), 2., 3.)
    return np.select(
        [L < math.log(3000), L <= 553/50, L <= 11509/1000,
         L <= 1179/100, L <= 1193/100, L <= 12337/1000, L < 100,
         L < 132, L <= 235, L < 240, L < 1.5e12, L < 2e12],
        [small, low, np.full_like(L, 61), np.minimum(67, P), np.minimum(71, P),
         np.minimum(73, P), P, np.minimum(P, np.minimum(G, A)), np.minimum(P, A),
         np.minimum(35000, A), gaussian_seeded_selected(L), (282924/1000000)*L**2],
        default=(2827/10000)*L**2)


TIGHT_LOW_PRIME_STEPS = [
    (23, 8032/1000), (29, 8271/1000), (31, 8934/1000),
    (37, 9339/1000), (41, 9532/1000), (43, 9902/1000),
    (47, 10422/1000), (53, 10907/1000), (59, 11062/1000),
]


def gaussian_recovered_bound(L: np.ndarray) -> np.ndarray:
    """Lean gaussianRecoveredBound: one large-index root, allowance 8.14, floor 12000."""
    return np.maximum(12000., gaussian_raw_bound(L, 407/50))


def gamma_recovered_bound(L: np.ndarray) -> np.ndarray:
    """Lean gammaRecoveredBound, whose fixed-stencil domain starts at L=101."""
    K, mu = 86733/98800, 11783423/25000000
    D, T = 36174637/11856000, 58129633/2223000
    v = mu*L+D
    radius = (v+np.sqrt(v*v+4*K*(7*L/6+T)))/(2*K)
    return (99/40)*radius**2


def gaussian_recovered_seeded(L: np.ndarray) -> np.ndarray:
    """Lean gaussianRecoveredSeeded: the exact selection of both clipped profiles."""
    s1, s2, s3 = (gaussian_switch(35000, 283/50), gaussian_switch(50000, 283/50),
                  gaussian_switch(50000, 136/25))
    return np.select(
        [L <= s1, L < s2, L <= s3],
        [np.full_like(L, 35000), gaussian_raw_bound(L, 283/50),
         np.full_like(L, 50000)], default=gaussian_raw_bound(L, 136/25))


def refined_candidates(L: np.ndarray) -> np.ndarray:
    """Independent guarded minimum defining Lean refinedWitnessEnvelope."""
    result = list(next_candidates(L))
    result.extend(np.where(L <= cap, float(b), np.inf)
                  for b, cap in TIGHT_LOW_PRIME_STEPS)
    result.extend([
        np.where(L >= 63, gaussian_recovered_bound(L), np.inf),
        np.where(L >= 101, gamma_recovered_bound(L), np.inf),
        np.where(L >= 63, np.maximum(35000, gaussian_raw_bound(L, 283/50)), np.inf),
        np.where(L >= 63, np.maximum(50000, gaussian_raw_bound(L, 136/25)), np.inf),
        np.where(L >= 1.1e12, (71/250)*L**2, np.inf),
        np.where(L >= 2e12, (28237/100000)*L**2, np.inf),
    ])
    return np.array(result)


def refined_upper(L: np.ndarray) -> np.ndarray:
    """Lean refinedSelectedEnvelope with its unchanged small-input convention.

    Evaluate the ordered low-prime selection first, then exactly the active analytic
    candidates. The independent candidates() check verifies the equivalent guarded min.
    """
    baseline = next_upper(L)
    low = np.select([L <= cap for _, cap in TIGHT_LOW_PRIME_STEPS],
                    [np.full_like(L, b) for b, _ in TIGHT_LOW_PRIME_STEPS],
                    default=baseline)
    base = np.where(L < math.log(3000), baseline, low)
    gaussian = gaussian_recovered_bound(L)
    gamma = gamma_recovered_bound(L)
    seeded = gaussian_recovered_seeded(L)
    return np.select(
        [L < 63, L < 101, L < 1.1e12, L < 2e12],
        [base, np.minimum.reduce([base, gaussian, seeded]),
         np.minimum.reduce([base, gaussian, gamma, seeded]),
         np.minimum.reduce([base, gaussian, gamma, seeded, (71/250)*L**2])],
        default=np.minimum.reduce([
            base, gaussian, gamma, seeded, (71/250)*L**2, (28237/100000)*L**2]))


FINITE_PRINCIPAL_STEPS = [
    (23, 8.087), (29, 8.325), (31, 8.987), (37, 9.390),
    (41, 9.583), (43, 9.952), (47, 10.471), (53, 10.955),
    (59, 11.109), (61, 11.546), (67, 11.830), (71, 11.970), (73, 12.373),
]
TRIANGULAR_PROFILES = [
    (7/15, 3e10), (21/50, 4e10), (1/3, 1e11), (3/10, 2.5e11),
    (29/100, 5e11), (71/250, 1.08e12), (2829/10000, 1.48e12),
    (1411811/5000000, 1.82e12),
]


def gaussian_floor_switch(u: float, D: float) -> float:
    d, beta, c = gaussian_coefficients()
    return (d*u*u-beta*u-D)/c


def gaussian_low_profile(L: np.ndarray, u: float, D: float) -> np.ndarray:
    return np.maximum((6/5)*u**4, gaussian_raw_bound(L, D))


def gaussian_low_family(L: np.ndarray) -> np.ndarray:
    """Exact rational-switch selection of the three low-floor profiles."""
    return np.select(
        [L <= gaussian_floor_switch(9.5, 9.3),
         L <= gaussian_floor_switch(9.8, 8.15)],
        [gaussian_low_profile(L, 9.1, 9.3), gaussian_low_profile(L, 9.5, 8.15)],
        default=gaussian_low_profile(L, 9.8, 8.13))


def gaussian_seeded_sharp(L: np.ndarray) -> np.ndarray:
    t1, t2, t3 = (gaussian_switch(35000, 5.63), gaussian_switch(50000, 5.63),
                  gaussian_switch(50000, 5.41))
    return np.select([L <= t1, L < t2, L <= t3],
        [np.full_like(L, 35000), gaussian_raw_bound(L, 5.63),
         np.full_like(L, 50000)], default=gaussian_raw_bound(L, 5.41))


def candidates(L: np.ndarray) -> np.ndarray:
    """Independent guarded minimum for Lean sharpWitnessEnvelope."""
    result = list(refined_candidates(L))
    result.extend(np.where(L <= cap, float(b), np.inf)
                  for b, cap in FINITE_PRINCIPAL_STEPS)
    result.extend(np.where(L >= 63, gaussian_low_profile(L, u, D), np.inf)
                  for u, D in [(9.1, 9.3), (9.5, 8.15), (9.8, 8.13)])
    result.extend(np.where(L >= 63, np.maximum(N, gaussian_raw_bound(L, D)), np.inf)
                  for N, D in [(35000, 5.63), (50000, 5.41)])
    result.extend(np.where(L >= T, C*L**2, np.inf) for C, T in TRIANGULAR_PROFILES)
    return np.array(result)


def upper(L: np.ndarray) -> np.ndarray:
    """Lean sharpSelectedEnvelope; 2047 <= n < 3000 retains value three."""
    baseline = refined_upper(L)
    finite = np.select([L <= cap for _, cap in FINITE_PRINCIPAL_STEPS],
        [np.minimum(baseline, b) for b, _ in FINITE_PRINCIPAL_STEPS], default=baseline)
    analytic = np.where(L < 63, finite,
        np.minimum.reduce([finite, gaussian_low_family(L), gaussian_seeded_sharp(L)]))
    # Entrances increase and coefficients decrease, so the last active profile wins.
    triangular = np.select([L < T for _, T in TRIANGULAR_PROFILES],
        [analytic] + [np.minimum(analytic, C*L**2) for C, _ in TRIANGULAR_PROFILES[:-1]],
        default=np.minimum(analytic, TRIANGULAR_PROFILES[-1][0]*L**2))
    return np.where(L < math.log(3000), baseline, triangular)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=ROOT / "doc/figures")
    parser.add_argument("--max-power", type=int, default=1024)
    args = parser.parse_args()
    if args.max_power < 1:
        parser.error("--max-power must be a positive integer")
    if args.max_power > 8192:
        parser.error("--max-power must not exceed 8192")
    args.output_dir.mkdir(parents=True, exist_ok=True)
    plt.rcParams.update({"font.size": 11, "svg.hashsalt": "mr-comparison",
                         "axes.spines.top": False, "axes.spines.right": False})

    Lmax = args.max_power * math.log(10)
    Lc = shifted_endpoint_w1000_crossing(73 / 50)
    entrances = np.array([math.log(500), math.log(1053), math.log(1120),
                          math.log(2047), math.log(3000), 56 / 5, 286 / 25,
                          23 / 2, 74 / 5, 43 / 4, 22, 111 / 4, 63, 209, gamma_fixed_switch(),
                          81 / 8, 171 / 8, 217 / 8,
                          5581 / 200, 523 / 50, 2171 / 100, 1373 / 50,
                          144 / 5, 120, 122, 330, 500, 5283 / 20, Lc, 81 / 4, 26, 1339 / 50, 703 / 20,
                          10367 / 200, 1706 / 25, 6671 / 50, 26269 / 100,
                          210, 240, 250, 258, 300, 11255, 34971, 46330,
                          shift117_minus_two_crossing(), 50880, 350000,
                          4000, 9565217391305 * math.log(10)])
    entrances = np.concatenate([entrances, [45/4, 2877/250, 47/4, 100, 112,
        gamma_sharp_switch(), gaussian_switch(35000, 29/5), gaussian_switch(50000, 29/5),
        gaussian_switch(50000, 111/20), 2e12]])
    entrances = np.concatenate([entrances, [cap for _, cap in LOW_PRIME_STEPS],
        [11509/1000, 1179/100, 1193/100, 12337/1000, 100, 132, 235, 240,
         gaussian_switch(35000,567/100), gaussian_switch(50000,567/100),
         gaussian_switch(50000,109/20), 1.5e12, 2e12]])
    entrances = np.concatenate([entrances, [cap for _, cap in TIGHT_LOW_PRIME_STEPS],
        [63, 101, 108, 126, 132, 215, 235, 1.1e12, 1.5e12, 2e12,
         gaussian_switch(35000, 283/50), gaussian_switch(50000, 283/50),
         gaussian_switch(50000, 136/25)]])
    entrances = np.concatenate([entrances,
        [cap for _, cap in FINITE_PRINCIPAL_STEPS], [T for _, T in TRIANGULAR_PROFILES],
        [gaussian_floor_switch(u, D) for u, D in
            [(9.1, 9.3), (9.5, 9.3), (9.5, 8.15), (9.8, 8.15), (9.8, 8.13)]],
        [gaussian_switch(N, D) for N, D in [(35000, 5.63), (50000, 5.63), (50000, 5.41)]]])
    entrances = entrances[entrances <= Lmax]
    L = np.unique(np.concatenate([
        np.exp(np.linspace(math.log(math.log(9)), math.log(Lmax), 10000)),
        entrances, np.nextafter(entrances, -np.inf), np.nextafter(entrances, np.inf),
        [math.log(9), Lmax],
    ]))
    U = upper(L)
    # These checks are finite runtime comparisons, separate from Lean interval proofs.
    # Keep the fixed baseline independent from the new candidates and interval selection.
    np.testing.assert_allclose(next_upper(L), np.min(next_candidates(L), axis=0),
                               rtol=3e-15)
    assert np.all(U <= next_upper(L)*(1+3e-15))
    np.testing.assert_allclose(previous_upper(L), np.min(previous_candidates(L), axis=0),
                               rtol=3e-15)
    np.testing.assert_allclose(U, np.min(candidates(L), axis=0), rtol=2e-15)
    assert upper(np.array([np.nextafter(math.log(2047), -np.inf)]))[0] == 2
    assert upper(np.array([math.log(2047)]))[0] == 3
    assert np.all(U > 0) and np.all(U <= L**2)

    # These finite numerical checks supplement the Lean continuous interval proofs.
    np.testing.assert_array_equal(upper(np.array([math.log(2047),
        np.nextafter(math.log(2047), np.inf)])), [3., 3.])
    assert np.all(U <= compatible_upper(L)*(1+2e-15))
    probe = np.unique(np.concatenate([np.geomspace(240, 4e13, 10000),
        [1.1e12, np.nextafter(1.1e12, -np.inf), np.nextafter(1.1e12, np.inf),
         1.5e12, np.nextafter(1.5e12, -np.inf), np.nextafter(1.5e12, np.inf),
         2e12, np.nextafter(2e12, -np.inf), np.nextafter(2e12, np.inf)]]))
    high_boundaries = np.array([T for _, T in TRIANGULAR_PROFILES])
    probe = np.unique(np.concatenate([probe, high_boundaries,
        np.nextafter(high_boundaries, -np.inf), np.nextafter(high_boundaries, np.inf)]))
    np.testing.assert_allclose(upper(probe), np.min(candidates(probe), axis=0), rtol=3e-15)
    assert np.all(upper(probe) <= compatible_upper(probe)*(1+3e-15))
    assert np.all(upper(probe) <= next_upper(probe)*(1+3e-15))
    gamma_strict = np.linspace(108., 126., 1001)
    single_strict = np.linspace(132., 235., 2001)
    earlier_strict = np.linspace(1.1e12, np.nextafter(1.5e12, -np.inf), 1001)
    sharper_strict = np.geomspace(2e12, 4e13, 1001)
    for interval in [gamma_strict, single_strict, earlier_strict, sharper_strict]:
        assert np.all(upper(interval) < next_upper(interval))
    old_single_strict = np.linspace(132., 215., 1001)
    assert np.all(np.maximum(12000., gaussian_raw_bound(old_single_strict, 163/20))
                  < next_upper(old_single_strict))
    for (bound, old_cap), (new_bound, new_cap) in zip(LOW_PRIME_STEPS,
                                                    TIGHT_LOW_PRIME_STEPS):
        assert bound == new_bound and old_cap < new_cap
        segment = np.linspace(np.nextafter(old_cap, np.inf), new_cap, 17)
        assert np.all(refined_upper(segment) == float(bound))
        assert np.all(upper(segment) < next_upper(segment))
        assert refined_upper(np.array([np.nextafter(new_cap, np.inf)]))[0] > bound
    for scale in [L, probe]:
        selected = gaussian_recovered_seeded(scale)
        profiles = np.minimum(np.maximum(35000, gaussian_raw_bound(scale, 283/50)),
                              np.maximum(50000, gaussian_raw_bound(scale, 136/25)))
        np.testing.assert_allclose(selected, profiles, rtol=3e-15)
    seed_switches = [gaussian_switch(35000, 283/50),
                     gaussian_switch(50000, 283/50), gaussian_switch(50000, 136/25)]
    assert 240 < seed_switches[0] < seed_switches[1] < seed_switches[2] < 295
    assert 209 < gamma_sharp_switch() < 210
    assert 240 < gaussian_switch(35000, 29/5) < 242
    assert 293 < gaussian_switch(50000, 29/5) < gaussian_switch(50000, 111/20) < 294

    # Current-baseline strict cells and the normal-range monotonicity check.
    assert np.all(U <= refined_upper(L)*(1+3e-15))
    assert np.all(np.diff(U) >= -1e-9)
    gaussian_band = np.linspace(100, 235, 3001)
    assert np.all(upper(gaussian_band) < refined_upper(gaussian_band))
    for old, new in zip(TIGHT_LOW_PRIME_STEPS, FINITE_PRINCIPAL_STEPS[:9]):
        b, old_cap = old
        segment = np.linspace(np.nextafter(old_cap, np.inf), new[1], 31)
        assert np.all(upper(segment) == b)
        assert np.all(upper(segment) < refined_upper(segment))
    for lo, hi, b in [(11.52, 11.53, 61), (11.8, 11.82, 67),
                      (11.94, 11.96, 71), (12.35, 12.37, 73)]:
        cell = np.linspace(lo, hi, 51)
        assert np.all(upper(cell) == b)
        assert np.all(upper(cell) < refined_upper(cell))
    for lo, hi in [(3e10, np.nextafter(1.1e12, -np.inf)), (1.82e12, 4e13)]:
        cell = np.geomspace(lo, hi, 3001)
        assert np.all(upper(cell) < refined_upper(cell))
    for scale in [L, probe]:
        np.testing.assert_allclose(gaussian_low_family(scale), np.minimum.reduce([
            gaussian_low_profile(scale, 9.1, 9.3), gaussian_low_profile(scale, 9.5, 8.15),
            gaussian_low_profile(scale, 9.8, 8.13)]), rtol=4e-15)
        np.testing.assert_allclose(gaussian_seeded_sharp(scale), np.minimum(
            np.maximum(35000, gaussian_raw_bound(scale, 5.63)),
            np.maximum(50000, gaussian_raw_bound(scale, 5.41))), rtol=4e-15)

    data = DATA_DIR / "mr_records.csv"
    with data.open(encoding="utf-8", newline="") as f:
        records = list(csv.DictReader(f))
    ns = [int(r["n"]) for r in records]
    ps = [int(r["witness"]) for r in records]
    assert len(records) == 11 and ps[-1] == 43
    assert all(a < b for a, b in zip(ns, ns[1:]))
    assert all(a < b for a, b in zip(ps, ps[1:]))
    record_L = np.log(np.array(ns, dtype=float))
    assert np.all(np.array(ps) <= upper(record_L))
    for n, p in zip(ns, ps):
        d, s = n - 1, 0
        while d % 2 == 0:
            d //= 2
            s += 1
        def passes(a):
            x = pow(a, d, n)
            if x in (1, n - 1):
                return True
            for _ in range(1, s):
                x = x*x % n
                if x == n - 1:
                    return True
            return False
        primes = [a for a in range(2, p + 1)
                  if all(a % b for b in range(2, math.isqrt(a) + 1))]
        assert primes[-1] == p and not passes(p)
        assert all(passes(a) for a in primes[:-1])

    fig, ax = plt.subplots(figsize=(12, 8))
    fig.subplots_adjust(left=.09, right=.95, top=.87, bottom=.13)
    ax.plot(np.log(L), U, color="#d55e00", linewidth=2.5,
            label=r"Pointwise bound $U_{\mathrm{MR}}(n)$ (comparison table)", zorder=3)
    ax.plot(np.log(L), L**2, color="#333333", linewidth=1.7, linestyle=":",
            label=r"$(\ln n)^2$", zorder=4)
    ax.step(np.log(record_L), ps, where="post", color="#007f80", linewidth=2,
            zorder=5)
    ax.scatter(np.log(record_L), ps, s=27, color="#007f80", zorder=7,
               label=r"Record points $Q_{\mathrm{MR}}(N)$ (OEIS A006945; prime bases 2, 3, 5, …)")
    ax.set_yscale("log")
    ax.set_xlim(math.log(math.log(9)), math.log(Lmax))
    ax.set_ylim(1, Lmax**2 * 1.2)
    powers = [2**k for k in range(14) if 2**k < args.max_power] + [args.max_power]
    power_ticks(ax, powers)
    ax.set_xlabel(r"Odd composite integer $n$ / upper bound $N$", labelpad=10)
    ax.set_ylabel("Least prime witness / upper bound")
    ax.grid(which="major", color="#d8dde3", linewidth=.7)
    bit_powers = [64, 80, 128]
    bit_positions = [math.log(k * math.log(2)) for k in bit_powers]
    for x in bit_positions:
        ax.axvline(x, color="#7e91ac", linestyle="--", linewidth=.9, zorder=1)
    top = ax.secondary_xaxis("top")
    top.set_xticks(bit_positions, [rf"$2^{{{k}}}$" for k in bit_powers])
    top.tick_params(axis="x", colors="#536780", labelsize=10, pad=5)
    ax.legend(loc="upper left", framealpha=.97, fontsize=10)
    ax.set_title("Miller–Rabin: least-prime witness bounds", pad=46)

    inset = ax.inset_axes([.045, .53, .35, .28])
    keep = L >= math.log(3000)
    inset.plot(np.log(L[keep]), U[keep]/L[keep]**2, color="#d55e00", linewidth=2)
    inset.axhline(1, color="#333333", linestyle=":", linewidth=1.3)
    inset.set_yscale("log")
    inset.set_xlim(math.log(math.log(3000)), math.log(Lmax))
    inset.set_ylim(.3, 1.015)
    inset.yaxis.set_major_locator(FixedLocator([.3, .4, .5, .6, .7, .8, .9, 1]))
    inset.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.2f}"))
    inset.yaxis.set_minor_locator(NullLocator())
    power_ticks(inset, [4, 8, 16, 32, 64, 128, 256, 512, 1024])
    inset.tick_params(labelsize=9)
    inset.set_title(r"Detail: $U_{\mathrm{MR}}(n)/(\ln n)^2$", fontsize=10)
    inset.grid(color="#e1e5e9", linewidth=.6)
    for x in bit_positions:
        inset.axvline(x, color="#7e91ac", linestyle="--", linewidth=.8, zorder=1)
    inset.set_facecolor("#fafbfd")
    stem = args.output_dir / "mr_upper_bound_comparison"
    fig.savefig(stem.with_suffix(".svg"), metadata={"Date": None})
    svg = stem.with_suffix(".svg")
    svg.write_text("\n".join(line.rstrip() for line in svg.read_text(encoding="utf-8").splitlines())
                   + "\n", encoding="utf-8")
    fig.savefig(stem.with_suffix(".png"), dpi=180)
    plt.close(fig)
    report = {"small_interval_switch": 2047,
              "small_three_interval": [2047, 3000],
              "low_prime_steps": FINITE_PRINCIPAL_STEPS,
              "pointwise_radius_floor": 8, "pointwise_inverse_bisections": 64,
              "gaussian_profiles": [{"floor": u, "residual": D} for u, D in
                  [(9.1, 9.3), (9.5, 8.15), (9.8, 8.13)]],
              "gaussian_profile_switches": [gaussian_floor_switch(u, D) for u, D in
                  [(9.1, 9.3), (9.5, 9.3), (9.5, 8.15), (9.8, 8.15), (9.8, 8.13)]],
              "gaussian_prefix": 721769/200000,
              "gaussian_seeded_residuals": [5.63, 5.41],
              "gaussian_seeded_prefixes": [480743/100000, 2455769/500000],
              "gaussian_seeded_switches": [gaussian_switch(N, D) for N, D in
                  [(35000, 5.63), (50000, 5.63), (50000, 5.41)]],
              "triangular_log_entrances": [T for _, T in TRIANGULAR_PROFILES],
              "triangular_coefficients": [C for C, _ in TRIANGULAR_PROFILES],
              "lean_selected_envelope": "sharpSelectedEnvelope",
              "lean_selection_equality": "sharp_eq_selected",
              "comparison_baseline": "refinedSelectedEnvelope",
              "sampled_selection_equality_checked": True,
              "sampled_plot_monotonicity_checked": True,
              "gaussian_strict_sample_interval": [100, 235],
              "candidates_checked": len(candidates(L)),
              "plot_scale_points_checked": len(L), "high_scale_probe_count": len(probe),
              "record_points_checked": len(records)}
    print(json.dumps(report, indent=2))
    print(f"Wrote {stem}.svg and .png")


if __name__ == "__main__":
    main()
