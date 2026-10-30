/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds
public import Mathlib.NumberTheory.AbelSummation

/-! # Quantitative weighted Abel summation

Finite Mangoldt sums are compared with their main integrals on intervals starting at two.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a differentiable real weight with integrable derivative on `[2,x]`, Abel summation
expresses its finite Mangoldt sum using the main integral and the Chebyshev error.
The explicit lower endpoint term permits weights singular at zero. -/
theorem mangoldt_weighted_abel {x : ℝ} (hx : 2 ≤ x) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 2 x)) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * f n) -
        (∫ t : ℝ in (2 : ℝ)..x, f t) =
      (Chebyshev.psi x - x) * f x + 2 * f 2 -
        ∫ t : ℝ in (2 : ℝ)..x, (Chebyshev.psi t - t) * deriv f t := by
  have hc : ContinuousOn f (Set.Icc 2 x) := fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt
  have hf : IntervalIntegrable f MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hc.integrableOn_Icc
  have hdf : IntervalIntegrable (deriv f) MeasureTheory.volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hi
  have ht := hi.mul_continuousOn continuousOn_id isCompact_Icc
  have ht' : IntervalIntegrable (fun t : ℝ ↦ t * deriv f t) MeasureTheory.volume 2 x := by
    simpa only [id_eq, mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr ht
  have hψ :=
    integrableOn_mul_sum_Icc (fun n ↦ ArithmeticFunction.vonMangoldt n) (m := 0)
      (by norm_num only : (0 : ℝ) ≤ 2) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at hψ
  have hp :
    IntervalIntegrable (fun t : ℝ ↦ Chebyshev.psi t * deriv f t) MeasureTheory.volume 2 x := by
    simpa only [mul_comm] using (intervalIntegrable_iff_integrableOn_Icc_of_le hx).mpr hψ
  have hAbel :=
    sum_mul_eq_sub_integral_mul₁ (fun n ↦ ArithmeticFunction.vonMangoldt n)
      ArithmeticFunction.map_zero ArithmeticFunction.vonMangoldt_apply_one x hd hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at hAbel
  have hs :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * f n := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
    simp only [ArithmeticFunction.map_zero, mul_zero, add_zero, mul_comm]
  rw [hs] at hAbel
  have hFTC :=
    intervalIntegral.integral_deriv_mul_eq_sub (u := fun t : ℝ ↦ t) (u' := fun _ ↦ (1 : ℝ)) (v := f)
      (v' := deriv f) (fun t _ ↦ hasDerivAt_id t)
      (fun t ht ↦ (hd t (by simpa only [Set.uIcc_of_le hx] using ht)).hasDerivAt)
      intervalIntegrable_const hdf
  simp only [one_mul, intervalIntegral.integral_add hf ht'] at hFTC
  have he :
    (∫ t : ℝ in (2 : ℝ)..x, (Chebyshev.psi t - t) * deriv f t) =
      (∫ t : ℝ in (2 : ℝ)..x, Chebyshev.psi t * deriv f t) -
        ∫ t : ℝ in (2 : ℝ)..x, t * deriv f t := by
    simp only [sub_mul]
    exact intervalIntegral.integral_sub hp ht'
  rw [he, hAbel]
  simp only [intervalIntegral.integral_of_le hx] at hFTC ⊢
  have hc' :
    (∫ t in Set.Ioc 2 x, deriv f t * Chebyshev.psi t) =
      ∫ t in Set.Ioc 2 x, Chebyshev.psi t * deriv f t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t _
    exact mul_comm _ _
  rw [hc']
  nlinarith only [hFTC]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
