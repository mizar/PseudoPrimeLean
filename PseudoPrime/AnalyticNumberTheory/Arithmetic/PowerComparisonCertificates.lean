/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.NormNum

/-! # Fourth-power certificates for real-power comparisons -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For nonnegative a and b, the rational power bound a^(5/4) at most b follows from a^5 at most
b^4. Raise both sides to the positive fourth power and use real-power multiplication. This gives
kernel-checked rational envelopes for small Euler terms. -/
theorem rpow_five_fourths_le_of_pow_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 5 ≤ b ^ 4) :
    a ^ (5 / 4 : ℝ) ≤ b := by
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg ha _) hb (by norm_num only : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul ha]
  norm_num only [show (5 / 4 : ℝ) * 4 = 5 by norm_num only, Real.rpow_ofNat]
  exact h

/-- For nonnegative a and b, a lower bound b^4 at most a^m implies b at most a^(m/4).
Raise both sides to the positive fourth power. This converts rational power comparisons into
small exact integer inequalities without numerical real-power evaluation. -/
theorem rpow_lower_of_fourth_power {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (m : ℕ) (h : b ^ 4 ≤ a ^ m) :
    b ≤ a ^ ((m : ℝ) / 4) := by
  apply (Real.rpow_le_rpow_iff hb (Real.rpow_nonneg ha _) (by norm_num only : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul ha, div_mul_cancel₀ _ (by norm_num only : (4 : ℝ) ≠ 0), Real.rpow_natCast,
    Real.rpow_ofNat]
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
