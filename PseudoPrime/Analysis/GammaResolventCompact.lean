/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventDerivatives
public import PseudoPrime.Analysis.GammaCriticalLineDerivatives
public import PseudoPrime.Analysis.SecondDerivativeInterpolation
public import PseudoPrime.Analysis.GammaResolventTail

/-! # From finite Gamma resolvent samples to global domination

Actual curvature estimates reduce the compact interval to 8001 node inequalities.
Evenness and the previously certified tail extend domination to all real heights.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The scaled difference (1+t²)(g(t)-h(t)) between the signed resolvent
majorant and the Gamma norm density. Positive values certify pointwise domination. -/
noncomputable def gammaResolventScaledGap (t : ℝ) : ℝ :=
  gammaResolventScaled t - scaledGammaHalfLineNorm t

/-- If all 8001 nodes j/500 have scaled gap at least 1/25000, the gap is
at least 13/1000000 on [0,16]. The actual second derivatives have bounds 24 and 30;
apply the certified interpolation loss with their difference bounded by 54. -/
theorem gammaResolventScaledGap_lower_of_grid
    (hnodes : ∀ j : ℕ, j ≤ 8000 → 1 / 25000 ≤ gammaResolventScaledGap ((j : ℝ) / 500)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 16) : (13 / 1000000 : ℝ) ≤ gammaResolventScaledGap t := by
  apply
    lower_bound_on_zero_sixteen_of_grid_and_second_deriv_le (f' := fun x ↦
      gammaResolventScaledDeriv x - scaledGammaHalfLineNormDeriv x) (f'' := fun x ↦
      gammaResolventScaledSecondDeriv x - scaledGammaHalfLineNormSecondDeriv x) _ _ _ hnodes ht
  · intro x _hx
    exact (gammaResolvent_hasDerivAt_scaled x).sub (hasDerivAt_scaledGammaHalfLineNorm x)
  · intro x _hx
    exact (gammaResolvent_hasDerivAt_scaledDeriv x).sub (hasDerivAt_scaledGammaHalfLineNormDeriv x)
  · intro x hx
    have hg := gammaResolvent_abs_scaledSecondDeriv_lt x
    have hh := abs_scaledGammaHalfLineNormSecondDeriv_le_thirty hx.1
    have hu := le_abs_self (gammaResolventScaledSecondDeriv x)
    have hl := neg_abs_le (scaledGammaHalfLineNormSecondDeriv x)
    linarith only [hg, hh, hu, hl]

/-- The finite grid gap bounds imply Gamma domination on [0,16]. Use the
positive interpolation margin and cancel the strictly positive scaling factor 1+t². -/
theorem norm_Gamma_half_add_I_le_gammaResolvent_on_nonneg_of_grid
    (hnodes : ∀ j : ℕ, j ≤ 8000 → 1 / 25000 ≤ gammaResolventScaledGap ((j : ℝ) / 500)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 16) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ gammaResolventMajorant t := by
  have h := gammaResolventScaledGap_lower_of_grid hnodes ht
  have hp : 0 < gammaResolventScaledGap t :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 13 / 1000000) h
  change 0 < (1 + t ^ 2) * gammaResolventMajorant t - (1 + t ^ 2) * gammaHalfLineNorm t at hp
  have hs : 0 < 1 + t ^ 2 := add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg t)
  have hd : gammaHalfLineNorm t < gammaResolventMajorant t :=
    (mul_lt_mul_iff_right₀ hs).mp (sub_pos.mp hp)
  simpa only [gammaHalfLineNorm, norm_Gamma_half_add_I] using hd.le

/-- The 8001 grid gap inequalities imply Gamma domination at every real height.
Evenness covers negative ordinates, interpolation covers [0,16], and the proved
rational-exponential tail covers |t|≥16. Only finite node arithmetic remains as input. -/
theorem norm_Gamma_half_add_I_le_gammaResolvent_of_grid
    (hnodes : ∀ j : ℕ, j ≤ 8000 → 1 / 25000 ≤ gammaResolventScaledGap ((j : ℝ) / 500)) (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ gammaResolventMajorant t := by
  apply norm_Gamma_half_add_I_le_gammaResolvent_of_compact _ t
  intro x hx
  have h :=
    norm_Gamma_half_add_I_le_gammaResolvent_on_nonneg_of_grid hnodes
      (show |x| ∈ Set.Icc (0 : ℝ) 16 from ⟨abs_nonneg x, hx⟩)
  have he : Real.pi * |x| = |Real.pi * x| := by rw [abs_mul, abs_of_pos Real.pi_pos]
  simpa only [norm_Gamma_half_add_I, he, Real.cosh_abs, gammaResolventMajorant, sq_abs] using h

end PseudoPrime.Analysis
