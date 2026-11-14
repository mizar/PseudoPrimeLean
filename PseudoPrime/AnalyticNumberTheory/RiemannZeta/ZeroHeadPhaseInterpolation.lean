/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseDerivative
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Interpolation between finite critical-line phase samples -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A uniform bound M for twice the sum of absolute ordinates and endpoint
bounds B imply the phase bound `B + M * (b - a)^2 / 8` throughout a
nondegenerate interval. Apply the second-derivative interpolation bound to
the phase sum and its negative. -/
theorem phase_le_of_endpoint_bounds {n : ℕ} (g : Fin n → ℝ) {a b v B M : ℝ} (hab : a < b)
    (hM : 0 ≤ M) (hm : 2 * ∑ i, |g i| ≤ M) (ha : |zeroHeadPhase g a| ≤ B)
    (hb : |zeroHeadPhase g b| ≤ B) (hv : v ∈ Set.Icc a b) :
    |zeroHeadPhase g v| ≤ B + M * (b - a) ^ 2 / 8 := by
  have hd : ∀ x ∈ Set.Icc a b, HasDerivAt (zeroHeadPhase g) (zeroHeadPhaseDeriv g x) x := fun x hx ↦
    hasDerivAt_zeroHeadPhase g x
  have hd' : ∀ x ∈ Set.Icc a b, HasDerivAt (zeroHeadPhaseDeriv g) (zeroHeadPhaseDeriv2 g x) x :=
    fun x hx ↦ hasDerivAt_zeroHeadPhaseDeriv g x
  have hc : ∀ x ∈ Set.Icc a b, |zeroHeadPhaseDeriv2 g x| ≤ M := fun x hx ↦
    (abs_zeroHeadPhaseDeriv2_le g x).trans hm
  have hlow :=
    Analysis.lower_bound_on_interval_of_second_deriv_le hab hM hd hd'
      (fun x hx ↦ (abs_le.mp (hc x hx)).2) (abs_le.mp ha).1 (abs_le.mp hb).1 hv
  have hupp :=
    Analysis.lower_bound_on_interval_of_second_deriv_le hab hM (fun x hx ↦ (hd x hx).neg)
      (fun x hx ↦ (hd' x hx).neg)
      (fun x hx ↦ by simpa only [neg_neg] using neg_le_neg (abs_le.mp (hc x hx)).1)
      (neg_le_neg (abs_le.mp ha).2) (neg_le_neg (abs_le.mp hb).2) hv
  simp only [Pi.neg_apply] at hupp
  apply abs_le.mpr
  constructor <;> linarith only [hlow, hupp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
