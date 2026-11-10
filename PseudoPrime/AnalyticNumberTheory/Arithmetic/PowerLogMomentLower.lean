/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel

/-! # Lower Abel bounds for logarithmic Mangoldt moments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A differentiable lower envelope for Chebyshev psi bounds a finite
power-logarithm tail below when the weight decreases. Integration by parts
cancels the upper boundary and retains the exact lower boundary. -/
theorem mangoldt_moment_tail_lower_integral (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (E D : ℝ → ℝ) (hE : ∀ t ∈ Set.Icc a b, HasDerivAt E (D t) t) (hD : ContinuousOn D (Set.Icc a b))
    (hψ : ∀ t ∈ Set.Icc a b, E t ≤ Chebyshev.psi t)
    (hd : ∀ t ∈ Set.Icc a b, mangoldtMomentWeightDeriv σ k t ≤ 0) :
    mangoldtMomentWeight σ k a * (E a - Chebyshev.psi a) +
        ∫ t in Set.Ioc a b, D t * mangoldtMomentWeight σ k t ≤
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hEc : ContinuousOn E (Set.Icc a b) := fun t ht ↦ (hE t ht).continuousAt.continuousWithinAt
  have hWc : ContinuousOn (mangoldtMomentWeight σ k) (Set.Icc a b) := fun t ht ↦
    (mangoldt_moment_weight_deriv σ k (ha0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hWdc := mangoldt_moment_deriv_continuous σ k (b := b) ha0
  have hDi : IntervalIntegrable D MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hD.integrableOn_Icc
  have hWi : IntervalIntegrable (mangoldtMomentWeightDeriv σ k) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hWdc.integrableOn_Icc
  have hDW :
    IntervalIntegrable (fun t ↦ D t * mangoldtMomentWeight σ k t) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hD.mul hWc).integrableOn_Icc
  have hEW :
    IntervalIntegrable (fun t ↦ E t * mangoldtMomentWeightDeriv σ k t) MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hEc.mul hWdc).integrableOn_Icc
  have hpart :=
    intervalIntegral.integral_deriv_mul_eq_sub (u := E) (u' := D) (v := mangoldtMomentWeight σ k)
      (v' := mangoldtMomentWeightDeriv σ k)
      (fun t ht ↦ hE t (by simpa only [Set.uIcc_of_le hab] using ht))
      (fun t ht ↦ by
        have ht' : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using ht
        exact mangoldt_moment_weight_deriv σ k (ha0.trans_le ht'.1))
      hDi hWi
  rw [intervalIntegral.integral_add hDW hEW] at hpart
  simp only [intervalIntegral.integral_of_le hab] at hpart
  have heq :
    (∫ t in Set.Ioc a b, E t * mangoldtMomentWeightDeriv σ k t) =
      ∫ t in Set.Ioc a b, mangoldtMomentWeightDeriv σ k t * E t := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    exact mul_comm _ _
  rw [heq] at hpart
  have hw : 0 ≤ mangoldtMomentWeight σ k b := by
    exact
      mul_nonneg (Real.rpow_nonneg (by linarith only [ha, hab]) _)
        (pow_nonneg (Real.log_nonneg (ha.trans hab)) k)
  have hboundary := mul_le_mul_of_nonneg_left (hψ b ⟨hab, le_rfl⟩) hw
  have hpsiInt :
    MeasureTheory.IntegrableOn (fun t ↦ mangoldtMomentWeightDeriv σ k t * Chebyshev.psi t)
      (Set.Ioc a b) := by
    have hi :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (a := a) (b := b)
        (by linarith only [ha]) hWdc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at hi
    exact hi.mono_set Set.Ioc_subset_Icc_self
  have hEInt :
    MeasureTheory.IntegrableOn (fun t ↦ mangoldtMomentWeightDeriv σ k t * E t) (Set.Ioc a b) :=
    (hWdc.mul hEc).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hint :=
    MeasureTheory.setIntegral_mono_on hpsiInt hEInt measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonpos_left (hψ t ⟨ht.1.le, ht.2⟩) (hd t ⟨ht.1.le, ht.2⟩))
  have habel := mangoldt_moment_finite_abel σ k ha0 hab
  linarith only [hboundary, hint, habel, hpart]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
