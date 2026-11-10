/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel

/-! # Finite lower Abel bounds for logarithmic Mangoldt moments -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A continuous lower envelope for `ψ` bounds a finite power-logarithm
moment tail below when the weight is nonnegative and decreasing. Abel
summation keeps the actual lower boundary and reverses the integral comparison. -/
theorem mangoldt_moment_tail_lower (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (E : ℝ → ℝ)
    (hE : ContinuousOn E (Set.Icc a b)) (hψ : ∀ t ∈ Set.Icc a b, E t ≤ Chebyshev.psi t)
    (hd : ∀ t ∈ Set.Icc a b, mangoldtMomentWeightDeriv σ k t ≤ 0) :
    mangoldtMomentWeight σ k b * E b - mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, mangoldtMomentWeightDeriv σ k t * E t ≤
      (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb1 : 1 ≤ b := ha.trans hab
  have hw : 0 ≤ mangoldtMomentWeight σ k b := by
    exact
      mul_nonneg (Real.rpow_nonneg (by linarith only [hb1]) _) (pow_nonneg (Real.log_nonneg hb1) k)
  have hboundary := mul_le_mul_of_nonneg_left (hψ b ⟨hab, le_rfl⟩) hw
  have hc := mangoldt_moment_deriv_continuous σ k (b := b) ha0
  have hpsiInt :
    MeasureTheory.IntegrableOn (fun t ↦ mangoldtMomentWeightDeriv σ k t * Chebyshev.psi t)
      (Set.Ioc a b) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (a := a) (b := b)
        (by linarith only [ha]) hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hEInt :
    MeasureTheory.IntegrableOn (fun t ↦ mangoldtMomentWeightDeriv σ k t * E t) (Set.Ioc a b) :=
    (hc.mul hE).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hint :=
    MeasureTheory.setIntegral_mono_on hpsiInt hEInt measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonpos_left (hψ t ⟨ht.1.le, ht.2⟩) (hd t ⟨ht.1.le, ht.2⟩))
  have habel := mangoldt_moment_finite_abel σ k ha0 hab
  linarith only [habel, hboundary, hint]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
