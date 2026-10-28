/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TriangularUpperScaledIntegrals

/-! # Finite alpha-18 upper-support Mangoldt bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Under a Chebyshev error constant 13 at positive scale, the finite
upper-support Mangoldt sum differs from its Abel main term by at most
13(12 exp 9 - 48)x^(3/4). Check integrability before separating the error. -/
theorem triangular18_upper_mangoldt_error_le {x : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ 13 * t ^ (3 / 4 : ℝ)) :
    |(∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
            ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
              ArithmeticFunction.vonMangoldt k) -
          (-36 * x -
            ∫ t in x..(Real.exp 36 * x),
              (((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x) * t)| ≤
      13 * (12 * Real.exp 9 - 48) * x ^ (3 / 4 : ℝ) := by
  let a := x
  let b := Real.exp 36 * x
  let d := fun t : ℝ ↦ ((t / x) ^ (-3 / 2 : ℝ) * (Real.log (t / x) / 2 - 19)) / x
  have ha : 0 < a := hx
  have he : (1 : ℝ) ≤ Real.exp 36 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hab : a ≤ b := (one_mul x).symm.trans_le (mul_le_mul_of_nonneg_right he hx.le)
  have hc : ContinuousOn d (Set.Icc a b) := by
    intro t ht
    have hp := div_pos (lt_of_lt_of_le ha ht.1) hx
    have hr :=
      (Real.continuousAt_rpow_const (t / x) (-3 / 2) (Or.inl hp.ne')).comp (f := fun z : ℝ ↦ z / x)
        (x := t) (continuousAt_id.div_const x)
    have hl :=
      (Real.continuousAt_log hp.ne').comp (f := fun z : ℝ ↦ z / x) (x := t)
        (continuousAt_id.div_const x)
    exact ((hr.mul ((hl.div_const 2).sub continuousAt_const)).div_const x).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (fun t ↦ d t * Chebyshev.psi t) (Set.Ioc a b) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) ha.le hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hj : MeasureTheory.IntegrableOn (fun t ↦ d t * t) (Set.Ioc a b) :=
    (hc.mul continuousOn_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hsub :
    (∫ t in a..b, d t * (Chebyshev.psi t - t)) =
      (∫ t in a..b, d t * Chebyshev.psi t) - ∫ t in a..b, d t * t := by
    simp only [mul_sub]
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hab, MeasureTheory.integral_sub hi hj]
  have hi := triangular18_upper_psi_error_integral_le hx hpsi
  have he := mul_le_mul_of_nonneg_left (hpsi x hx.le) (by norm_num only : (0 : ℝ) ≤ 36)
  have ht := abs_sub (-36 * (Chebyshev.psi x - x)) (∫ t in a..b, d t * (Chebyshev.psi t - t))
  rw [abs_mul, show |(-36 : ℝ)| = 36 by norm_num only] at ht
  have h :
    |-36 * (Chebyshev.psi x - x) - ∫ t in a..b, d t * (Chebyshev.psi t - t)| ≤
      13 * (12 * Real.exp 9 - 48) * x ^ (3 / 4 : ℝ) := by
    change |∫ t in a..b, d t * (Chebyshev.psi t - t)| ≤ _ at hi
    nlinarith only [hi, he, ht]
  rw [hsub] at h
  rw [triangular18_upper_mangoldt_boundary hx, ← intervalIntegral.integral_of_le hab]
  change
    |(-36 * Chebyshev.psi x - ∫ t in a..b, d t * Chebyshev.psi t) -
          (-36 * x - ∫ t in a..b, d t * t)| ≤
      _
  convert h using 1
  congr 1
  ring

/-- Under a Chebyshev error constant 13 at positive scale, the finite
upper-support Mangoldt sum is at most x(4 exp 18 - 76) plus its explicit error.
Evaluate the scaled main integral and take the upper side of the absolute error bound. -/
theorem triangular18_upper_mangoldt_sum_le {x : ℝ} (hx : 0 < x)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ 13 * t ^ (3 / 4 : ℝ)) :
    (∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊Real.exp 36 * x⌋₊,
        ((36 - Real.log ((k : ℝ) / x)) * ((k : ℝ) / x) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k) ≤
      x * (4 * Real.exp 18 - 76) + 13 * (12 * Real.exp 9 - 48) * x ^ (3 / 4 : ℝ) := by
  have h := triangular18_upper_mangoldt_error_le hx hpsi
  rw [triangular18_upper_scaled_main_integral hx] at h
  have hl := (abs_le.mp h).2
  linarith only [hl]

end PseudoPrime.Analysis
