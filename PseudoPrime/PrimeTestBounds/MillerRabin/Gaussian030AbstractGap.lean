/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Gaussian030Parameters

/-! # Scalar Gaussian gap for logarithmic scale at least 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The explicit Gaussian high-range inequality holds for the chosen radius
once the square-root, logarithm, and negative-power remainders meet the stated
simple bounds. The rational margins are valid uniformly for `L ≥ 1000`. -/
theorem gaussian030_abstract_gap {L r t z q : ℝ} (hL : 1000 ≤ L) (hr : r = (377 / 1000 : ℝ) * L)
    (ht : 19 ≤ t) (htL : t ≤ L / 50) (hz : z ≤ r / 20) (hq : q ≤ 1 / r) :
    (20115621 / 25000000 : ℝ) * L +
        (4 * (7 / 50) * ((32 / 63) * (21 / 10) * (7 / 20) + (231 / 2500) * (29 / 20) / (7 / 20))) *
          t +
        1339 / 50000 +
        (4 * (7 / 50) * (231 / 2500) / (7 / 20)) / t +
        (12 * (2129 / 2000) + (7 / 3) * (2129 / 2000) * L + 4 * (7 / 50) * (1839 / 1000) +
            4 * (1839 / 1000) * z +
            8) /
          r +
        (512 / 9) / r ^ 2 +
        (1419 / 10) * q <
      (4 * (81470555 / 100000000) - 2129 / 2000) * r := by
  have hrL : 377 ≤ r := by
    rw [hr]; linarith only [hL]
  have hr0 : 0 < r := by linarith only [hrL]
  have ht0 : 0 < t := by linarith only [ht]
  have hmain :
    (11 / 500 : ℝ) * L ≤
      (4 * (81470555 / 100000000 : ℝ) - 2129 / 2000) * r - (20115621 / 25000000 : ℝ) * L := by
    rw [hr]
    linarith only [hL]
  have hV :
    (4 * (7 / 50 : ℝ) * ((32 / 63) * (21 / 10) * (7 / 20) + (231 / 2500) * (29 / 20) / (7 / 20))) *
        t ≤
      L / 100 := by
    linarith only [ht, htL]
  have hwidth : (4 * (7 / 50 : ℝ) * (231 / 2500) / (7 / 20)) / t ≤ 1 / 100 := by
    apply (div_le_iff₀ ht0).2
    linarith only [ht]
  have hterm :
    (12 * (2129 / 2000 : ℝ) + (7 / 3) * (2129 / 2000) * L + 4 * (7 / 50) * (1839 / 1000) +
          4 * (1839 / 1000) * z +
          8) /
        r ≤
      15 / 2 := by
    apply (div_le_iff₀ hr0).2
    rw [hr] at hz ⊢
    linarith only [hL, hz]
  have hquad : (512 / 9 : ℝ) / r ^ 2 ≤ 1 / 100 := by
    apply (div_le_iff₀ (sq_pos_of_pos hr0)).2
    nlinarith only [hrL]
  have hq' : (1419 / 10 : ℝ) * q ≤ 2 / 5 := by
    have hb : (1419 / 10 : ℝ) * (1 / r) ≤ 2 / 5 := by
      rw [show (1419 / 10 : ℝ) * (1 / r) = (1419 / 10 : ℝ) / r by ring]
      apply (div_le_iff₀ hr0).2
      linarith only [hrL]
    exact (mul_le_mul_of_nonneg_left hq (by norm_num only)).trans hb
  linarith only [hmain, hV, hwidth, hterm, hquad, hq', hL]

end PseudoPrime.PrimeTestBounds.MillerRabin
