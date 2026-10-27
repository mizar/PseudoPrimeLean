/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneDeciShiftSeparation

/-! # Scale-dependent reciprocal error in the quadratic odd-prime comparison -/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- At root y, retain the actual even reciprocal main error in the effective
loss, instead of its constant upper bound. The Riemann loss is 789/500.
This is the numerical input for the three primitive dyadic branches. -/
noncomputable def qNeOneScaleReciprocalLoss (y : ℝ) : ℝ :=
  789 / 500 + Analysis.primitiveReciprocalEvenMainError (y ^ 2) + 4 / 5

/-- For y at least eight, the scale-dependent loss is no larger than
1483/1000. Apply the certified even error bound and rational arithmetic.
This compares the variable condition with the published fixed-loss condition. -/
theorem qNeOneScaleReciprocalLoss_le {y : ℝ} (hy : (8 : ℝ) ≤ y) :
    qNeOneScaleReciprocalLoss y ≤ 1483 / 1000 := by
  have h :=
    Analysis.primitiveReciprocalEvenMainError_le_neg_179_div_200 (Analysis.sq_ge_64_of_ge_8 hy)
  unfold qNeOneScaleReciprocalLoss
  linarith only [h]

/-- For arbitrary envelope inputs, the exact difference in loss is multiplied
by the displayed positive-scale factor. Expand the envelope and normalize.
This quantifies savings without changing any conductor or dyadic terms. -/
theorem qNeOneReciprocalUpper_sub_eq (y f r s d : ℝ) :
    qNeOneReciprocalUpper y f r d - qNeOneReciprocalUpper y f s d =
      (2 * y + 2 + 2 * Real.log y) * (r - s) / (1 - 1 / y) ^ 2 := by
  unfold qNeOneReciprocalUpper
  ring

/-- Above root eight, increasing the loss increases the upper envelope.
Use its exact difference and positivity of the scale factor.
This transports any sharper reciprocal estimate into the witness comparison. -/
theorem qNeOneReciprocalUpper_mono_loss {y f r s d : ℝ} (hy : (8 : ℝ) ≤ y) (hrs : r ≤ s) :
    qNeOneReciprocalUpper y f r d ≤ qNeOneReciprocalUpper y f s d := by
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have hc : 0 ≤ 2 * y + 2 + 2 * Real.log y := by linarith only [hy, hz]
  apply sub_nonneg.mp
  rw [qNeOneReciprocalUpper_sub_eq]
  exact div_nonneg (mul_nonneg hc (sub_nonneg.mpr hrs)) (sq_nonneg _)

/-- Under GRH, the conductor conditions and the three possible values at two,
the scale-dependent separation rules out odd-prime triviality. Apply the
generic transfer with the actual even error and the Riemann loss 789/500.
This retains the error dependence needed for subsequent cutoff improvements. -/
theorem not_oddPrimeTrivial_of_scale_reciprocal_separation {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y L : ℝ} (hy : (8 : ℝ) ≤ y)
    (hlog4 : Real.log χ.conductor ≤ L + Real.log 4)
    (hlogOdd : χ.primitiveCharacter 2 ≠ 0 → Real.log χ.conductor ≤ L)
    (hcases : χ.primitiveCharacter 2 = 0 ∨ χ.primitiveCharacter 2 = 1 ∨ χ.primitiveCharacter 2 = -1)
    (hsep :
      qNeOneReciprocalUpper y (L + Real.log 4 - Real.log Real.pi) (qNeOneScaleReciprocalLoss y)
          (Real.log 2) <
        qNeOneReciprocalLower y) :
    ¬OddPrimeTrivial χ (y ^ 2) := by
  exact
    not_oddPrimeTrivial_of_reciprocal_loss_and_mainError χ hne heven hGRH hy (le_refl _) hlog4
      hlogOdd hcases
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_789_div_500
        hGRH.riemann (le_trans (by norm_num only) (Analysis.sq_ge_64_of_ge_8 hy)))
      hsep

/-- Above root eight, the scale-dependent upper envelope is no larger than
the fixed envelope used by the one-tenth correction. Combine loss monotonicity
and the uniform error bound. Thus the variable separation is a weaker requirement. -/
theorem qNeOneScaleReciprocalUpper_le_retained {y f : ℝ} (hy : (8 : ℝ) ≤ y) :
    qNeOneReciprocalUpper y f (qNeOneScaleReciprocalLoss y) (Real.log 2) ≤
      qNeOneReciprocalUpper y f (1483 / 1000) (Real.log 2) := by
  exact qNeOneReciprocalUpper_mono_loss hy (qNeOneScaleReciprocalLoss_le hy)

end PseudoPrime.LLS.Extensions
