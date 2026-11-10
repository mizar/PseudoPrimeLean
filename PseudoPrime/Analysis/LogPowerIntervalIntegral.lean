/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerTailIntegral

/-! # Power-logarithm integrals on finite intervals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Evaluate a logarithmic power times a negative real power over `[a,b]`.
The same primitive used for infinite tails gives the difference of the two
endpoint polynomials. -/
theorem log_power_interval_integral {r a b : ℝ} (hr : 0 < r) (ha : 1 ≤ a) (hab : a ≤ b) (k : ℕ) :
    (∫ t in Set.Ioc a b, Real.log t ^ k * t ^ (-r - 1)) =
      a ^ (-r) * logPowerTailPoly r k (Real.log a) -
        b ^ (-r) * logPowerTailPoly r k (Real.log b) := by
  have hi : MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t ^ k * t ^ (-r - 1)) (Set.Ioc a b) :=
    (log_power_tail_integrable hr ha k).mono_set Set.Ioc_subset_Ioi_self
  have hi' :
    IntervalIntegrable (fun t : ℝ ↦ Real.log t ^ k * t ^ (-r - 1)) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hi
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        log_power_tail_primitive_deriv hr
          (zero_lt_one.trans_le
            (ha.trans (show t ∈ Set.Icc a b by simpa only [Set.uIcc_of_le hab] using ht).1))
          k)
      hi'
  rw [intervalIntegral.integral_of_le hab] at h
  linarith only [h]

end PseudoPrime.Analysis
