/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalLog

/-! # Internally certified logarithm of two -/

public section

namespace PseudoPrime.Analysis

-- Forty rational Taylor terms require deeper recursive reduction.
set_option maxRecDepth 4096 in
/-- The logarithm of two is enclosed by the displayed 35-decimal rational
interval. The finite forty-term certificate is checked by `decide_cbv` and
transported using the analytic logarithm remainder theorem. -/
theorem log_two_35_bounds :
    (69314718055994530941723212145817656 / 100000000000000000000000000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (69314718055994530941723212145817657 / 100000000000000000000000000000000000 : ℝ) := by
  have hc :
    mantissaLog40Check 2
        (69314718055994530941723212145817656 / 100000000000000000000000000000000000)
        (69314718055994530941723212145817657 / 100000000000000000000000000000000000) =
      true := by
    unfold mantissaLog40Check rationalMantissaLog40
    decide_cbv
  have h := mantissaLog40Check_sound hc
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- Certified log-two bounds scale to every natural power of two. This
supplies cached power-of-two logarithms without new finite Taylor computations. -/
theorem log_two_pow_bounds (n : ℕ) :
    (n : ℝ) * (69314718055994530941723212145817656 / 100000000000000000000000000000000000 : ℝ) ≤
        Real.log ((2 : ℝ) ^ n) ∧
      Real.log ((2 : ℝ) ^ n) ≤
        (n : ℝ) *
          (69314718055994530941723212145817657 / 100000000000000000000000000000000000 : ℝ) := by
  rw [Real.log_pow]
  exact
    ⟨mul_le_mul_of_nonneg_left log_two_35_bounds.1 (Nat.cast_nonneg n),
      mul_le_mul_of_nonneg_left log_two_35_bounds.2 (Nat.cast_nonneg n)⟩

/-- The cutoff-512 logarithm inherits its certified interval from nine times
log two. It is used in the grouped EM8 endpoint correction. -/
theorem log_512_bounds :
    (9 : ℝ) * (69314718055994530941723212145817656 / 100000000000000000000000000000000000 : ℝ) ≤
        Real.log 512 ∧
      Real.log 512 ≤
        (9 : ℝ) *
          (69314718055994530941723212145817657 / 100000000000000000000000000000000000 : ℝ) := by
  have h := log_two_pow_bounds 9
  norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 9 = 512 by norm_num only] at h
  norm_num only at ⊢
  exact h

end PseudoPrime.Analysis
