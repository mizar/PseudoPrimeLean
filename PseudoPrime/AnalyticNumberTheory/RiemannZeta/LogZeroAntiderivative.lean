/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogZeroIntegration

/-! # Antiderivatives of logarithmic zero terms

Evaluate the finite zero-ledger integrals and pass to their limit.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Integrate a complex power over `0 < a ≤ b`, provided its exponent is
not `-1`. Differentiate the standard complex-power antiderivative. -/
theorem integral_cpow_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hρ : ρ + 1 ≠ 0) :
    ∫ x in a..b, (x : ℂ) ^ ρ = ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ + 1) := by
  have hderiv :
    ∀ t ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ ↦ (y : ℂ) ^ (ρ + 1) / (ρ + 1)) ((t : ℂ) ^ ρ) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ (0 : ℝ) := ne_of_gt (lt_of_lt_of_le ha ht.1)
    have h := (hasDerivAt_ofReal_cpow_const ht0 hρ).div_const (ρ + 1)
    have heq : (ρ + 1) * (t : ℂ) ^ (ρ + 1 - 1) / (ρ + 1) = (t : ℂ) ^ ρ := by
      rw [mul_comm, mul_div_assoc, div_self hρ, mul_one, show (ρ + 1 - 1 : ℂ) = ρ from by ring]
    rwa [heq] at h
  have hint : IntervalIntegrable (fun x : ℝ ↦ (x : ℂ) ^ ρ) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact
      (Complex.continuousAt_ofReal_cpow_const t ρ
          (Or.inr (ne_of_gt (lt_of_lt_of_le ha ht.1)))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [sub_div]

/-- For a nontrivial zeta zero and positive ordered endpoints, integrate its
logarithmic zero term using the complex-power antiderivative. The nonnegative
real part guarantees that the exponent plus one is nonzero. -/
theorem integral_logZeroTerm {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) :
    ∫ x in a..b, nontrivialLogZeroTerm x ρ =
      -(riemannZetaZeroMultiplicity ρ : ℂ) * (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ + 1)) /
        ρ ^ 2 := by
  have hρ : ρ + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith only [hr, hre]
  simp only [nontrivialLogZeroTerm, hz, hre, and_self, ↓reduceIte, riemannZetaLogZeroContribution]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    integral_cpow_pos ha hab hρ]

/-- For `1 ≤ a ≤ b`, the evaluated finite sums of integrated logarithmic
zero terms converge to the integral of the full zero sum. Apply the individual
antiderivative formula to each zero in the finite ledger. -/
theorem evaluated_zero_integrals_limit {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          -(riemannZetaZeroMultiplicity ρ : ℂ) *
              (((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) / (ρ + 1)) /
            ρ ^ 2)
      Filter.atTop (nhds (∫ x in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
  apply (zero_integrals_limit ha hab).congr'
  filter_upwards with m
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hmem := Finset.mem_filter.mp hρ
  exact
    integral_logZeroTerm (zero_lt_one.trans_le ha) hab
      (mem_riemannZetaZerosInAnyRectangle_iff.mp hmem.1).2 (not_lt.mp hmem.2)

/-- For a nontrivial zeta zero and positive ordered endpoints, combine the
integrated logarithmic zero term with its two boundary terms. Algebra reduces
the denominator to the product of the zero and its successor. -/
theorem boundary_zero {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hre : 0 ≤ ρ.re) :
    (b : ℂ) * nontrivialLogZeroTerm b ρ - (a : ℂ) * nontrivialLogZeroTerm a ρ -
        (∫ x in a..b, nontrivialLogZeroTerm x ρ) =
      -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
        (ρ * (ρ + 1)) := by
  have hρ1 : ρ + 1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hr
    linarith only [hr, hre]
  have ha0 : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le ha hab).ne'
  rw [integral_logZeroTerm ha hab hz hre]
  simp only [nontrivialLogZeroTerm, hz, hre, and_self, ↓reduceIte, riemannZetaLogZeroContribution]
  rw [Complex.cpow_add _ _ ha0, Complex.cpow_add _ _ hb0]
  simp only [Complex.cpow_one]
  by_cases hρ : ρ = 0
  · norm_num only [hρ, div_zero, mul_zero, sub_zero]
  · have hi : ρ⁻¹ * ρ = 1 := inv_mul_cancel₀ hρ
    have hj : (ρ + 1)⁻¹ * (ρ + 1) = 1 := inv_mul_cancel₀ hρ1
    simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    linear_combination
      (riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) * (b : ℂ) ^ ρ - (a : ℂ) * (a : ℂ) ^ ρ) *
        (ρ⁻¹ ^ 2 * hj - ρ⁻¹ * (ρ + 1)⁻¹ * hi)

/-- For `1 < a ≤ b`, the finite sums of the simplified zero contributions
converge to the full zero-series boundary terms minus its interval integral.
Combine the endpoint ledger limits with the integrated ledger limit. -/
theorem boundary_limit {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          -(riemannZetaZeroMultiplicity ρ : ℂ) * ((b : ℂ) ^ (ρ + 1) - (a : ℂ) ^ (ρ + 1)) /
            (ρ * (ρ + 1)))
      Filter.atTop
      (nhds
        ((b : ℂ) * (∑' ρ : ℂ, nontrivialLogZeroTerm b ρ) -
          (a : ℂ) * (∑' ρ : ℂ, nontrivialLogZeroTerm a ρ) -
          ∫ x in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
  classical
  let S : ℕ → Finset ℂ := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  have hterm (x : ℝ) (hx : 1 < x) :
    Filter.Tendsto (fun m : ℕ ↦ ∑ ρ ∈ S m, nontrivialLogZeroTerm x ρ) Filter.atTop
      (nhds (∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
    apply (log_zero_tsum_limit hx).congr'
    filter_upwards with m
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hmem := Finset.mem_filter.mp hρ
    have hz := (mem_riemannZetaZerosInAnyRectangle_iff.mp hmem.1).2
    simp only [nontrivialLogZeroTerm, hz, true_and, not_lt.mp hmem.2, ↓reduceIte]
  have hlim :=
    (((hterm b (lt_of_lt_of_le ha hab)).const_mul (b : ℂ)).sub ((hterm a ha).const_mul (a : ℂ))).sub
      (zero_integrals_limit ha.le hab)
  apply hlim.congr'
  filter_upwards with m
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hmem := Finset.mem_filter.mp hρ
  exact
    boundary_zero (zero_lt_one.trans ha) hab (mem_riemannZetaZerosInAnyRectangle_iff.mp hmem.1).2
      (not_lt.mp hmem.2)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
