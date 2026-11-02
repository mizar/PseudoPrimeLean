/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsHighParameters

/-! # Lower bound for the high-range paired binomial ratio -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under the high-range radius, logarithm, floor, and ceiling bounds, the
paired binomial base `2 * (M + 1 - k) / (k + 1)` exceeds `(7 / 6) * b`.
The natural subtraction is justified by `k ≤ M`; the floor and ceiling
errors are absorbed by the added ones. This is the scalar input for the
uniform logarithmic kernel budget. -/
theorem high_paired_ratio_lower {L b u σ : ℝ} {M k : ℕ} (hL : 1024 ≤ L)
    (hb : (2 / 3 : ℝ) * L - 1 ≤ b) (hbhalf : L / 2 ≤ b) (hu0 : 0 < u) (hu : u ≤ L / 64) (hσ : σ ≤ 1)
    (hkM : k ≤ M) (hM : ((9 / 10 : ℝ) * b ^ 2) / u < (M : ℝ) + 1) (hk : (k : ℝ) < σ * L / u) :
    (7 / 6 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by
  have hb0 : 0 < b := by linarith only [hL, hbhalf]
  have hpart : (7 / 6 : ℝ) * (L + u) < (9 / 5 : ℝ) * b - 4 := by linarith only [hL, hb, hu]
  have hmul := mul_lt_mul_of_pos_left hpart hb0
  have hbound : 2 * L ≤ 4 * b := by linarith only [hbhalf]
  have hbase : (7 / 6 : ℝ) * b * (L + u) < 2 * ((9 / 10 : ℝ) * b ^ 2 - L) := by
    nlinarith only [hmul, hbound]
  have hSL : σ * L ≤ L := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hσ) (show (0 : ℝ) ≤ L by linarith only [hL])]
  have hstrong : (7 / 6 : ℝ) * b * (σ * L + u) < 2 * ((9 / 10 : ℝ) * b ^ 2 - σ * L) := by
    have hmul' := mul_nonneg (sub_nonneg.mpr hSL) hb0.le
    nlinarith only [hbase, hSL, hmul']
  have hmk : ((M + 1 - k : ℕ) : ℝ) = (M : ℝ) + 1 - k := by
    rw [Nat.cast_sub (hkM.trans (Nat.le_succ M)), Nat.cast_succ]
  have hN : ((9 / 10 : ℝ) * b ^ 2 - σ * L) < ((M + 1 - k : ℕ) : ℝ) * u := by
    have hm := (div_lt_iff₀ hu0).mp hM
    have hkk := (lt_div_iff₀ hu0).mp hk
    nlinarith only [hm, hkk, hmk]
  have hK : ((k : ℝ) + 1) * u < σ * L + u := by
    have hkk := (lt_div_iff₀ hu0).mp hk
    linarith only [hkk]
  have hleft := mul_lt_mul_of_pos_left hK (show 0 < (7 / 6 : ℝ) * b by positivity)
  have hright := mul_lt_mul_of_pos_left hN (show (0 : ℝ) < 2 by norm_num only)
  have hden : 0 < (k : ℝ) + 1 := by positivity
  apply (lt_div_iff₀ hden).2
  have hv : (7 / 6 : ℝ) * b * ((k : ℝ) + 1) * u < (2 * ((M + 1 - k : ℕ) : ℝ)) * u := by
    nlinarith only [hleft, hstrong, hright]
  exact lt_of_mul_lt_mul_right hv hu0.le

/-- For `L ≥ 1024` and `0 < σ ≤ 1`, the paired binomial base for the
specified floor radius, floor supply, and ceiling-minus-one exponent exceeds
`(7 / 6) * b`. The established parameter bounds discharge the general ratio
estimate uniformly for both high-range structural branches. -/
theorem high_selected_ratio_lower {L σ : ℝ} (hL : 1024 ≤ L) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    (7 / 6 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) := by
  dsimp only
  let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  have hb := high_radius_floor_lower hL
  have hb1 : 1 < b := by linarith only [hL, hb.2.1]
  have hu : 0 < u := mul_pos (by norm_num only) (Real.log_pos hb1)
  have hσL : 0 < σ * L / u := div_pos (mul_pos hσ0 (by linarith only [hL])) hu
  apply
    high_paired_ratio_lower hL hb.1.le hb.2.1 hu (high_floor_two_log_bounds hL).1.le hσ1
      (high_exponent_le_supply hL hσ0 hσ1)
  · exact Nat.lt_floor_add_one (((9 / 10 : ℝ) * b ^ 2) / u)
  · exact (ceil_sub_one_bounds hσL).2

/-- The selected high-range ratio has logarithm greater than `u / 2 + 3 / 20`,
where `u = 2 * log b`. The ratio exceeds `(7 / 6) * b`; a rational Taylor
certificate bounds `log (7 / 6)` below by more than `3 / 20`. -/
theorem high_selected_ratio_log {L σ : ℝ} (hL : 1024 ≤ L) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) :
    let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
    let u := 2 * Real.log b
    let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
    let k := ⌈σ * L / u⌉₊ - 1
    u / 2 + 3 / 20 < Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) := by
  dsimp only
  let b : ℝ := (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ)
  let u := 2 * Real.log b
  let M := ⌊((9 / 10 : ℝ) * b ^ 2) / u⌋₊
  let k := ⌈σ * L / u⌉₊ - 1
  have hb : 0 < b := by
    have hf := (high_radius_floor_lower hL).2.1
    linarith only [hL, hf]
  have hc : Analysis.rationalLogIntervalCheck (7 / 6) 0 12 (151 / 1000) 1 = true := by
    decide +kernel
  have hconst := (Analysis.rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hconst
  have hpos : 0 < (7 / 6 : ℝ) * b := mul_pos (by norm_num only) hb
  have hratio : (7 / 6 : ℝ) * b < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1) :=
    high_selected_ratio_lower hL hσ0 hσ1
  have hlog := Real.log_lt_log hpos hratio
  rw [Real.log_mul (by norm_num only : (7 / 6 : ℝ) ≠ 0) hb.ne'] at hlog
  linarith only [hconst, hlog]

/-- A positive logarithmic scale with the high-range quadratic margin and an
exponent at least `σ * L / u - 1` gives `σ * L / 2 < k * (u / 2 + 3 / 20)`
when `σ ≥ 2 / 3`. Divide the margin by `u` and multiply the exponent bound;
this is the scalar kernel-count budget. -/
theorem high_kernel_scalar_budget {L σ u k : ℝ} (hL : 0 < L) (hσ : (2 / 3 : ℝ) ≤ σ) (hu : 0 < u)
    (hmargin : u ^ 2 + (3 / 10 : ℝ) * u < L / 5) (hk : σ * L / u - 1 ≤ k) :
    σ * L / 2 < k * (u / 2 + 3 / 20) := by
  have hσL : (2 / 3 : ℝ) * L ≤ σ * L := mul_le_mul_of_nonneg_right hσ hL.le
  have hbound : u ^ 2 + (3 / 10 : ℝ) * u < (3 / 10) * (σ * L) := by linarith only [hmargin, hσL]
  have hpos : 0 ≤ u / 2 + (3 / 20 : ℝ) := by linarith only [hu]
  have hmul := mul_le_mul_of_nonneg_right hk hpos
  have hcancel : (σ * L / u) * u = σ * L := div_mul_cancel₀ _ hu.ne'
  have hmulbound : (u ^ 2 + (3 / 10 : ℝ) * u) / u < (3 / 10) * (σ * L) / u :=
    (div_lt_div_iff_of_pos_right hu).2 hbound
  have huCancel : (u ^ 2 + (3 / 10 : ℝ) * u) / u = u + 3 / 10 := by field_simp
  rw [huCancel] at hmulbound
  have hdiv : (3 / 10 : ℝ) * (σ * L) / u = (3 / 10) * (σ * L / u) := by ring
  rw [hdiv] at hmulbound
  nlinarith only [hmul, hcancel, hmulbound]

end PseudoPrime.PrimeTestBounds.MillerRabin
