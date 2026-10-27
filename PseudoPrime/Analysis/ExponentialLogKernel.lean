/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampLogKernel

/-! # Finite logarithmic reconstruction of the exponential weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For 0<v<=y, reconstruct exp(-v) from the clipped logarithmic variation
integral through y and its two endpoint terms. Apply the smooth primitive and
cancel the moving lower endpoint. This is the finite atom identity whose
boundary terms vanish when passing to the full exponential sum. -/
theorem exponential_log_atom {v y : ℝ} (hv : 0 < v) (hvy : v ≤ y) :
    Real.exp (-v) =
      (∫ u in (0 : ℝ)..y, positiveLogRatio v u * ((u - 1) * Real.exp (-u))) +
        y * Real.exp (-y) * Real.log (y / v) +
        Real.exp (-y) := by
  rw [clipped_integral_from_join hv hv.le hvy
      (show Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) from
        (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg))]
  have hi :
    IntervalIntegrable (fun u : ℝ ↦ Real.log (u / v) * ((u - 1) * Real.exp (-u)))
      MeasureTheory.volume v y :=
    (show ContinuousOn (fun u : ℝ ↦ Real.log (u / v) * ((u - 1) * Real.exp (-u))) (Set.uIcc v y)
        from
        ((show ContinuousOn (fun u : ℝ ↦ Real.log (u / v)) (Set.uIcc v y) from fun u hu ↦
              (log_div_derivative hv
                  (hv.trans_le ((Set.uIcc_of_le hvy) ▸ hu).1)).continuousAt.continuousWithinAt).mul
          ((continuous_id.sub continuous_const).mul
              (Real.continuous_exp.comp continuous_id.neg)).continuousOn)).intervalIntegrable
  have he :=
    log_variation_integral hv hv hvy (fun u _ ↦ exponentialRamp_first_derivative u)
      (fun u _ ↦ exponentialRamp_first_variation u) hi
  rw [he, Real.log_div_self]
  ring

end PseudoPrime.Analysis
