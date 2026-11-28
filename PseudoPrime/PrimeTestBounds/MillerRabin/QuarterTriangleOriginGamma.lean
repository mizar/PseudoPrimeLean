/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleOrigin
public import PseudoPrime.Analysis.EulerMascheroniBounds

/-! # Origin gamma series for the wide triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive exponential correction at pole 2k+1/2 in the origin gamma series. -/
noncomputable def triangleOriginTerm (k : ℕ) : ℝ :=
  (1 - Real.exp (-((2 * k + 1 / 2) * (5 / 2)))) / (2 * k + 1 / 2) ^ 2

/-- The poles from index two onward are dominated by consecutive differences
of reciprocals, so their tail is bounded by 1/7. -/
private theorem originTerm_step (k : ℕ) :
    triangleOriginTerm (k + 2) ≤ 1 / (4 * k + 7) - 1 / (4 * k + 11) := by
  unfold triangleOriginTerm
  push_cast
  apply le_trans (div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (sq_nonneg _))
  field_simp
  nlinarith only [Nat.cast_nonneg (α := ℝ) k]

/-- The full positive series is at most 79/25, retaining the exponential
at the first pole and summing the reciprocal differences from the third pole. -/
theorem triangle_origin_series_upper : (∑' k : ℕ, triangleOriginTerm k) ≤ 79 / 25 := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 7 / 2) (j := 2) (n := 40) (lo := 5 / 4) (hi := 2)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have he := (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 7 / 2)).mp hlog
  have hinv := one_div_le_one_div_of_le (Real.exp_pos _) he
  rw [one_div (Real.exp _), ← Real.exp_neg] at hinv
  have h0 : triangleOriginTerm 0 ≤ 20 / 7 := by
    norm_num only [triangleOriginTerm, Nat.cast_zero, mul_zero, zero_add]
    linarith only [hinv]
  have h1 : triangleOriginTerm 1 ≤ 4 / 25 := by
    unfold triangleOriginTerm
    norm_num only [Nat.cast_one, mul_one]
    linarith only [(Real.exp_pos (-((2 + 1 / 2) * (5 / 2)))).le]
  have hpartial (n : ℕ) :
    (∑ k ∈ Finset.range (n + 2), triangleOriginTerm k) ≤ 79 / 25 - 1 / (4 * n + 7) := by
    induction n with
    | zero =>
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Nat.cast_zero,
        mul_zero]
      linarith only [h0, h1]
    | succ n ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      have hd : (4 * ((n : ℝ) + 1) + 7) = 4 * n + 11 := by ring
      rw [hd]
      linarith only [ih, originTerm_step n]
  apply Real.tsum_le_of_sum_range_le
  · intro n
    unfold triangleOriginTerm
    apply div_nonneg _ (sq_nonneg _)
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  · intro n
    cases n with
    | zero => norm_num only [Finset.sum_range_zero]
    | succ n =>
      cases n with
      | zero =>
        change (∑ i ∈ Finset.range 1, triangleOriginTerm i) ≤ _
        rw [Finset.sum_range_one]
        linarith only [h0]
      | succ n => exact (hpartial n).trans (sub_le_self _ (by positivity))

/-- The series expression for the origin gamma constant at half-width 5/2. -/
noncomputable def triangleOriginGamma : ℝ :=
  -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 - Real.log Real.pi +
    (4 / 5) * ∑' k : ℕ, triangleOriginTerm k

/-- The origin gamma constant in series form is strictly below -2.84. -/
theorem triangle_origin_gamma_upper : triangleOriginGamma < -(284 / 100) := by
  have hp : (314 / 100 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d6]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 314 / 100) (j := 2) (n := 40) (lo := 1144 / 1000)
        (hi := 2) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hl := (Real.log_le_log (by norm_num only) hp)
  unfold triangleOriginGamma
  linarith only [Analysis.twentyThree_fortieths_lt_eulerMascheroniConstant, Real.pi_gt_d6,
    Real.log_two_gt_d9, hlog, hl, triangle_origin_series_upper]

/-- Combining the origin prime mass with the signed gamma series yields the
strict correction used in each of the three character bounds of section 76. -/
theorem triangle_origin_correction :
    28 / 5 <
      2 *
          (∑ m ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊,
            ArithmeticFunction.vonMangoldt m / Real.sqrt m * (1 - Real.log m / (5 / 2))) -
        triangleOriginGamma := by
  linarith only [triangle_center_mass_lower, triangle_origin_gamma_upper]

end PseudoPrime.PrimeTestBounds.MillerRabin
