/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.NumberTheory.Chebyshev

/-! # Abel summation for logarithmic Mangoldt moments -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The power-logarithm weight for a Dirichlet moment. It is evaluated on
positive arguments and used with the von Mangoldt function in Abel summation. -/
noncomputable def mangoldtMomentWeight (σ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ (-σ) * Real.log t ^ k

/-- The explicit derivative of the power-logarithm moment weight on the
positive half-line. This form preserves both contributions of the product rule. -/
noncomputable def mangoldtMomentWeightDeriv (σ : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (-σ) * t ^ (-σ - 1) * Real.log t ^ k + t ^ (-σ) * ((k : ℝ) * Real.log t ^ (k - 1) * t⁻¹)

/-- Differentiate the power-logarithm weight at a positive argument using
the real-power and logarithm derivative rules. -/
theorem mangoldt_moment_weight_deriv (σ : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (mangoldtMomentWeight σ k) (mangoldtMomentWeightDeriv σ k t) t := by
  have hd :=
    (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl ht.ne')).mul ((Real.hasDerivAt_log ht.ne').pow k)
  apply hd.congr_deriv
  dsimp only [mangoldtMomentWeightDeriv]
  rw [Real.rpow_sub ht, Real.rpow_one]
  simp only [Pi.pow_apply]

/-- For nonnegative exponent and input at least one, the power-logarithm
weight decreases once `σ * log t` reaches the logarithm degree. This sign is
the hypothesis used to bound a Chebyshev-weighted tail by partial summation. -/
theorem mangoldt_moment_deriv_nonpos {σ t : ℝ} (k : ℕ) (hσ : 0 ≤ σ) (ht : 1 ≤ t)
    (hk : (k : ℝ) ≤ σ * Real.log t) : mangoldtMomentWeightDeriv σ k t ≤ 0 := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hp : t ^ (-σ - 1) = t ^ (-σ) * t⁻¹ := by
    rw [Real.rpow_sub ht0, Real.rpow_one, div_eq_mul_inv]
  cases k with
  | zero =>
    simp only [mangoldtMomentWeightDeriv, Nat.cast_zero, zero_mul, mul_zero, add_zero, pow_zero,
      mul_one]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ) (Real.rpow_nonneg ht0.le _)
  | succ k =>
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
    have hnonneg : 0 ≤ t ^ (-σ) * t⁻¹ * Real.log t ^ k :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg ht0.le _) (inv_nonneg.mpr ht0.le))
        (pow_nonneg hlog k)
    dsimp only [mangoldtMomentWeightDeriv]
    rw [hp]
    simp only [Nat.succ_sub_one, pow_succ]
    calc
      _ = (t ^ (-σ) * t⁻¹ * Real.log t ^ k) * ((k.succ : ℝ) - σ * Real.log t) := by ring
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hnonneg (sub_nonpos.mpr hk)

/-- The moment-weight derivative is continuous on every interval bounded
away from zero, which supplies the integrability needed in Abel summation. -/
theorem mangoldt_moment_deriv_continuous (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (mangoldtMomentWeightDeriv σ k) (Set.Icc a b) := by
  intro t ht
  have hp := lt_of_lt_of_le ha ht.1
  have hl := Real.continuousAt_log hp.ne'
  have hp1 := Real.continuousAt_rpow_const t (-σ - 1) (Or.inl hp.ne')
  have hp2 := Real.continuousAt_rpow_const t (-σ) (Or.inl hp.ne')
  have hi := continuousAt_inv₀ hp.ne'
  exact
    (((continuousAt_const.mul hp1).mul (hl.pow k)).add
        (hp2.mul ((continuousAt_const.mul (hl.pow (k - 1))).mul hi))).continuousWithinAt

/-- On a positive finite interval, Abel summation expresses a logarithmic
Mangoldt moment tail in terms of its Chebyshev boundary values and derivative
integral. The interval is open at the lower arithmetic cutoff. -/
theorem mangoldt_moment_finite_abel (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n =
      mangoldtMomentWeight σ k b * Chebyshev.psi b - mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, mangoldtMomentWeightDeriv σ k t * Chebyshev.psi t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) :=
    mangoldt_moment_weight_deriv σ k (lt_of_lt_of_le ha ht.1)
  have he :
    Set.EqOn (deriv (mangoldtMomentWeight σ k)) (mangoldtMomentWeightDeriv σ k) (Set.Icc a b) :=
    fun t ht ↦ (hd t ht).deriv
  have hc := mangoldt_moment_deriv_continuous σ k (b := b) ha
  have hi : MeasureTheory.IntegrableOn (deriv (mangoldtMomentWeight σ k)) (Set.Icc a b) :=
    (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- A continuous upper envelope for Chebyshev psi bounds a finite moment
tail when the power-logarithm weight is nonnegative and decreasing. The exact
lower boundary term is retained for a subsequent infinite-tail estimate. -/
theorem mangoldt_moment_tail_upper (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (E : ℝ → ℝ)
    (hE : ContinuousOn E (Set.Icc a b)) (hψ : ∀ t ∈ Set.Icc a b, Chebyshev.psi t ≤ E t)
    (hd : ∀ t ∈ Set.Icc a b, mangoldtMomentWeightDeriv σ k t ≤ 0) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) ≤
      mangoldtMomentWeight σ k b * E b - mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b, mangoldtMomentWeightDeriv σ k t * E t := by
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
    MeasureTheory.setIntegral_mono_on hEInt hpsiInt measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonpos_left (hψ t ⟨ht.1.le, ht.2⟩) (hd t ⟨ht.1.le, ht.2⟩))
  have habel := mangoldt_moment_finite_abel σ k ha0 hab
  linarith only [habel, hboundary, hint]

/-- If the Chebyshev envelope is differentiable, integration by parts
cancels the upper boundary in the finite moment-tail bound. The result retains
the exact lower boundary and the integral of the weight against the envelope
derivative, ready for an infinite-tail limit. -/
theorem mangoldt_moment_tail_upper_integral (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (E D : ℝ → ℝ) (hE : ∀ t ∈ Set.Icc a b, HasDerivAt E (D t) t) (hD : ContinuousOn D (Set.Icc a b))
    (hψ : ∀ t ∈ Set.Icc a b, Chebyshev.psi t ≤ E t)
    (hd : ∀ t ∈ Set.Icc a b, mangoldtMomentWeightDeriv σ k t ≤ 0) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, mangoldtMomentWeight σ k n * ArithmeticFunction.vonMangoldt n) ≤
      mangoldtMomentWeight σ k a * (E a - Chebyshev.psi a) +
        ∫ t in Set.Ioc a b, D t * mangoldtMomentWeight σ k t := by
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
  have h := mangoldt_moment_tail_upper σ k ha hab E hEc hψ hd
  nlinarith only [h, hpart]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
