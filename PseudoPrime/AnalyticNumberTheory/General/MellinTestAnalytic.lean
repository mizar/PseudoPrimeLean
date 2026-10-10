/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestDecay

/-!
# Entire Mellin transforms of compact logarithmic tests

These results supply the analytic weights and finite zero ledgers used when
passing from weighted residue rectangles to an infinite zero sum.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For a compactly supported logarithmic test, its multiplicative weight vanishes
eventually both at infinity and at the positive side of zero. Pull eventual
vanishing back along the logarithm. These endpoint facts give every power bound
required for holomorphy of its Mellin transform. -/
theorem logarithmicTestWeight_eventually_zero (g : ℝ → ℂ) (hc : HasCompactSupport g) :
    (∀ᶠ x in Filter.atTop, logarithmicTestWeight g x = 0) ∧
      (∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), logarithmicTestWeight g x = 0) := by
  have hz : ∀ᶠ u in Filter.cocompact ℝ, g u = 0 := by
    simpa only [Filter.coclosedCompact_eq_cocompact, Filter.EventuallyEq, Pi.zero_apply] using
      (hasCompactSupport_iff_eventuallyEq.mp hc)
  constructor
  · filter_upwards [(Real.tendsto_log_atTop.mono_right atTop_le_cocompact).eventually hz] with x hx
    rw [logarithmicTestWeight, hx, smul_zero]
  · filter_upwards [(Real.tendsto_log_nhdsGT_zero.mono_right atBot_le_cocompact).eventually hz] with
      x hx
    rw [logarithmicTestWeight, hx, smul_zero]

/-- For a continuous logarithmic test, its multiplicative weight is locally
integrable on the positive half-line. Continuity of the logarithm, exponential
and scalar product gives continuity there. This supplies the local
integrability input for differentiating its Mellin transform. -/
theorem logarithmicTestWeight_locallyIntegrable (g : ℝ → ℂ) (hg : Continuous g) :
    MeasureTheory.LocallyIntegrableOn (logarithmicTestWeight g) (Set.Ioi 0) := by
  apply ContinuousOn.locallyIntegrableOn _ measurableSet_Ioi
  intro x hx
  have hl := Real.continuousAt_log (ne_of_gt hx)
  have hcont : ContinuousAt (logarithmicTestWeight g) x :=
    (Real.continuous_exp.continuousAt.comp (hl.neg.div_const 2)).smul (hg.continuousAt.comp hl)
  exact hcont.continuousWithinAt

/-- For a continuous compactly supported logarithmic test, its Mellin transform
is differentiable on the whole complex plane. The weight vanishes near both
multiplicative endpoints, so arbitrary power bounds place every complex point
inside a Mellin differentiability strip. This supplies analytic weights for
finite residue contours without an independent holomorphy premise. -/
theorem differentiable_mellin_logarithmicTestWeight (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : Continuous g) : Differentiable ℂ (mellin (logarithmicTestWeight g)) := by
  obtain ⟨ht, hb⟩ := logarithmicTestWeight_eventually_zero g hc
  intro s
  apply
    mellin_differentiableAt_of_isBigO_rpow (logarithmicTestWeight_locallyIntegrable g hg)
      ((Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-(s.re + 1))) Filter.atTop).congr'
        (Filter.EventuallyEq.symm ht) Filter.EventuallyEq.rfl)
      (by linarith only)
      ((Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-(s.re - 1)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr'
        (Filter.EventuallyEq.symm hb) Filter.EventuallyEq.rfl)
      (by linarith only)

end PseudoPrime.AnalyticNumberTheory.General
