/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseDerivative
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadDistance100
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Signed phase interpolation for the sinc-weighted estimate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Signed endpoint upper bounds control the true phase on a cell with the left endpoint
shifted by 1/2800. The height-100 ordinate brackets supply the curvature bound. -/
theorem signed_phase_shifted_cell (g : Fin 29 → ℝ) (hpos : ∀ i, 0 ≤ g i)
    (hu : LowZero100UpperBounds g) {a b v A B : ℝ} (hab : a ≤ b)
    (ha : zeroHeadPhase g (a - 1 / 2800) ≤ A) (hb : zeroHeadPhase g b ≤ B)
    (hv : v ∈ Set.Icc (a - 1 / 2800) b) :
    zeroHeadPhase g v ≤ max 0 (max A B) + 3611 * (b - a + 1 / 2800) ^ 2 / 8 := by
  let U := max 0 (max A B)
  have hleft : zeroHeadPhase g (a - 1 / 2800) ≤ U :=
    ha.trans ((le_max_left A B).trans (le_max_right 0 _))
  have hright : zeroHeadPhase g b ≤ U := hb.trans ((le_max_right A B).trans (le_max_right 0 _))
  have hcurv := (lowZero100_phase_curvature g hpos hu).le
  have hint :=
    Analysis.lower_bound_on_interval_of_second_deriv_le
      (show a - 1 / 2800 < b by linarith only [hab]) (show (0 : ℝ) ≤ 3611 by norm_num only)
      (fun x _ ↦ (hasDerivAt_zeroHeadPhase g x).neg)
      (fun x _ ↦ (hasDerivAt_zeroHeadPhaseDeriv g x).neg)
      (fun x _ ↦ (neg_le_abs _).trans ((abs_zeroHeadPhaseDeriv2_le g x).trans hcurv))
      (neg_le_neg hleft) (neg_le_neg hright) hv
  simp only [Pi.neg_apply] at hint
  change zeroHeadPhase g v ≤ U + _
  linarith only [hint]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
