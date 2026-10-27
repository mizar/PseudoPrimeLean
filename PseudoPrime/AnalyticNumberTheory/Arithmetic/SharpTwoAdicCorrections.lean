/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TwoAdicCorrections

/-! # Sharp finite logarithmic corrections at two -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For arbitrary real weights and a natural cutoff, evaluate the odd affine sum.
Pair successive exponents; the parity of the endpoint determines the last pair.
This exact formula supplies the half-square bound for a character of value minus one. -/
theorem odd_affine_sum_eq (a L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, if Odd k then 2 * (a * (L - k * a)) else 0) =
      if Odd K then (K + 1) * a * L - (K + 1) ^ 2 * a ^ 2 / 2
      else K * a * L - K ^ 2 * a ^ 2 / 2 := by
  induction K with
  | zero =>
    norm_num only [Finset.Icc_eq_empty_of_lt Nat.zero_lt_one, Finset.sum_empty, Nat.not_odd_zero,
      ↓reduceIte, Nat.cast_zero]
    ring
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le K)), ih]
    by_cases ho : Odd K
    · have hn : ¬Odd (K + 1) := Nat.not_odd_iff_even.mpr ho.add_one
      simp only [ho, hn, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring
    · have he : Even K := Nat.not_odd_iff_even.mp ho
      have hs : Odd (K + 1) := he.add_one
      simp only [ho, hs, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring

/-- For arbitrary real weights, completing the square bounds the odd affine sum.
No floor or positivity hypothesis is needed. This supplies the sharp logarithmic budget. -/
theorem odd_affine_sum_le_half_sq (a L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, if Odd k then 2 * (a * (L - k * a)) else 0) ≤ L ^ 2 / 2 := by
  rw [odd_affine_sum_eq]
  split_ifs
  · nlinarith only [sq_nonneg (L - ((K : ℝ) + 1) * a)]
  · nlinarith only [sq_nonneg (L - (K : ℝ) * a)]

/-- For a nonzero real cutoff and primitive value minus one at two, the exact odd
affine formula bounds the logarithmic defect by half the squared logarithm.
This removes the positive linear loss from the previous branch envelope. -/
theorem twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_neg_one {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : x ≠ 0) (h2 : χ.primitiveCharacter 2 = -1) :
    twoAdicLogCorrection x χ ≤ (Real.log x) ^ 2 / 2 := by
  rw [twoAdicLogCorrection_eq_odd_sum_of_apply_two_eq_neg_one x χ hx h2]
  exact odd_affine_sum_le_half_sq (Real.log 2) (Real.log x) _

/-- For real weights and any natural cutoff, retain the negative half-step shift
in the full affine sum. Complete the square in the exact arithmetic-sum formula.
The bound is the sharp zero-value branch input for the two-adic correction. -/
theorem affine_sum_le_shifted_half_sq (a L : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, a * (L - k * a)) ≤ (L - a / 2) ^ 2 / 2 := by
  have hi := two_mul_sum_log_weight a L K
  nlinarith only [hi, sq_nonneg (L - ((K : ℝ) + 1 / 2) * a)]

/-- For a nonzero cutoff and primitive value zero at two, the logarithmic correction
is bounded by the half-square with a half-log-two shift. Evaluate the zero powers
and use the exact affine-sum inequality. This retains the negative linear saving. -/
theorem twoAdicLogCorrection_le_shifted_half_log_sq_of_apply_two_eq_zero {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : x ≠ 0) (h2 : χ.primitiveCharacter 2 = 0) :
    twoAdicLogCorrection x χ ≤ (Real.log x - Real.log 2 / 2) ^ 2 / 2 := by
  rw [twoAdicLogCorrection_eq_sum x χ hx]
  calc
    _ = ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log 2 * (Real.log x - k * Real.log 2) :=
      by
      apply Finset.sum_congr rfl
      intro k hk
      have hk0 : k ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hk).1
      simp only [h2, zero_pow hk0, Complex.zero_re, mul_zero, sub_zero]
    _ ≤ _ := affine_sum_le_shifted_half_sq _ _ _

/-- For a quadratic primitive associate and a nonzero cutoff, every value at two
has correction at most half the squared logarithm. Split its three possible values.
This uniform envelope removes the old positive linear loss in the negative branch. -/
theorem twoAdicLogCorrection_le_half_log_sq_of_isQuadratic {q : ℕ} (x : ℝ)
    (χ : DirichletCharacter ℂ q) (hx : x ≠ 0) (hquad : χ.primitiveCharacter.IsQuadratic) :
    twoAdicLogCorrection x χ ≤ (Real.log x) ^ 2 / 2 := by
  rcases hquad (2 : ZMod χ.conductor) with h0 | h1 | hm
  · exact twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_zero x χ hx h0
  · exact twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_one x χ hx h1
  · exact twoAdicLogCorrection_le_half_log_sq_of_apply_two_eq_neg_one x χ hx hm

end PseudoPrime.AnalyticNumberTheory.Arithmetic
