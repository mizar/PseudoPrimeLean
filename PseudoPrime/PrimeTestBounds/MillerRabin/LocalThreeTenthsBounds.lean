/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDecimalScale
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDivisorLogBounds
public import PseudoPrime.LLS.DecimalLogBounds

/-! # Local bounds at coefficient three tenths -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A local modulus with `q² ≤ 10^9 n` has the envelope below `0.3 L²`
from logarithmic scale 250. Use `log(10) < 7/3` and the exact shifted-square
identity at the anchor 250. -/
theorem local_envelope_lt_of_square_le_log250 {n q : ℕ} (hn : 0 < n) (hL : 250 ≤ Real.log n)
    (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
  have hlog10 := log_ten_lt_seven_thirds
  have hlogq := local_log_le_of_square_le (Nat.cast_pos.mpr hn) hq hsize
  have hshift : 9 * Real.log 10 ≤ 21 := by nlinarith only [hlog10]
  have hqbound : Real.log q ≤ (Real.log n + 21) / 2 := by
    calc
      Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := hlogq
      _ ≤ (Real.log n + 21) / 2 := by nlinarith only [hshift]
  have hLpos : 0 < Real.log n := by linarith only [hL]
  have htsq : 0 ≤ (Real.log n - 250) ^ 2 := sq_nonneg _
  have hgapIdentity :
    (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 =
      (Real.log n - 250) ^ 2 / 20 + 29 * (Real.log n - 250) / 2 + 1559 / 4 := by
    ring
  have hgap : 0 < (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 := by
    rw [hgapIdentity]
    have ht : 0 ≤ Real.log n - 250 := by linarith only [hL]
    nlinarith only [ht, htsq]
  have hpoly : ((Real.log n + 21) / 2) ^ 2 < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    linarith only [hgap]
  have hLsq : (250 : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith only [hL]
  have hfloor : (3000 : ℝ) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hLsq]
  have hlogsq := mul_self_le_mul_self (Real.log_natCast_nonneg q) hqbound
  have hlogsq' : (Real.log q) ^ 2 ≤ ((Real.log n + 21) / 2) ^ 2 := by nlinarith only [hlogsq]
  exact max_lt hfloor (hlogsq'.trans_lt hpoly)

/-- A local modulus with `q² ≤ 10^9 n` has its old LLS envelope strictly
below `0.3 (log n)²` once `log n ≥ 240`. The shifted-square identity is
anchored at 240. -/
theorem local_envelope_lt_of_square_le_log240 {n q : ℕ} (hn : 0 < n) (hL : 240 ≤ Real.log n)
    (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
  have hlog10 := log_ten_lt_seven_thirds
  have hlogq := local_log_le_of_square_le (Nat.cast_pos.mpr hn) hq hsize
  have hshift : 9 * Real.log 10 ≤ 21 := by nlinarith only [hlog10]
  have hqbound : Real.log q ≤ (Real.log n + 21) / 2 := by
    calc
      Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := hlogq
      _ ≤ (Real.log n + 21) / 2 := by nlinarith only [hshift]
  have htsq : 0 ≤ (Real.log n - 240) ^ 2 := sq_nonneg _
  have hgapIdentity :
    (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 =
      (Real.log n - 240) ^ 2 / 20 + 27 * (Real.log n - 240) / 2 + 999 / 4 := by
    ring
  have hgap : 0 < (3 / 10 : ℝ) * (Real.log n) ^ 2 - ((Real.log n + 21) / 2) ^ 2 := by
    rw [hgapIdentity]
    have ht : 0 ≤ Real.log n - 240 := by linarith only [hL]
    nlinarith only [ht, htsq]
  have hpoly : ((Real.log n + 21) / 2) ^ 2 < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    linarith only [hgap]
  have hLsq : (240 : ℝ) ^ 2 ≤ (Real.log n) ^ 2 := by nlinarith only [hL]
  have hfloor : (3000 : ℝ) < (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hLsq]
  have hlogsq := mul_self_le_mul_self (Real.log_natCast_nonneg q) hqbound
  have hlogsq' : (Real.log q) ^ 2 ≤ ((Real.log n + 21) / 2) ^ 2 := by nlinarith only [hlogsq]
  exact max_lt hfloor (hlogsq'.trans_lt hpoly)

end PseudoPrime.PrimeTestBounds.MillerRabin
