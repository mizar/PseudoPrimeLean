/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail

/-! # Checked centered tail constants -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Inverse-square tail constants in thousandths for the two high kernels. -/
@[expose]
public def highCenteredTailTicks : HighGaussianKernel → ℕ
  | .k186 => 521
  | .k196 => 529

/-- Both integer-dot-product calculations fit their respective tail constants. -/
private theorem centered_tail_ticks_check (K : HighGaussianKernel) :
    centeredTailFast K ≤ (highCenteredTailTicks K : ℚ) / 1000 := by cases K <;> decide +kernel

/-- The rational expression used by the series theorem is below the checked scalar cap. -/
private theorem centered_tail_scalar (K : HighGaussianKernel) :
    (highCenteredTailRat K 36 : ℝ) ≤ (highCenteredTailTicks K : ℝ) / 1000 := by
  have h := centered_tail_ticks_check K
  rw [centered_tail_fast_eq] at h
  have hh : (highCenteredTailRat K 36 : ℝ) ≤ ((((highCenteredTailTicks K : ℚ) / 1000) : ℚ) : ℝ) :=
    Rat.cast_le.mpr h
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hh

/-- The checked constants give the inverse-square multiplier bound above height 100. -/
public theorem high_centered_tail_ticks_le (K : HighGaussianKernel) {t : ℝ} (ht : 100 < t) :
    ‖highPrincipalMultiplier K t‖ ≤ ((highCenteredTailTicks K : ℝ) / 1000) / t ^ 2 := by
  exact
    (high_centered_tail_le K ht).trans
      (div_le_div_of_nonneg_right ((high_centered_tail_rat_le K 36).trans (centered_tail_scalar K))
        (sq_nonneg _))

/-- The normalized principal series uses the checked scalar charge for the two-sided tail. -/
public theorem high_centered_series_ticks_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        ((highCenteredTailTicks K : ℝ) / 1000) * (13 / 1000) := by
  exact
    (high_centered_series_le K hRH 36 hc hX).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (centered_tail_scalar K) (by norm_num only)))

end PseudoPrime.PrimeTestBounds.MillerRabin
