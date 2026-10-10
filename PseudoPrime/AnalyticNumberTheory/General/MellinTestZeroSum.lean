/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.GenusConvergence
public import PseudoPrime.AnalyticNumberTheory.General.EntireOrder
public import PseudoPrime.AnalyticNumberTheory.General.FunctionalEquationZeros
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestStripDecay

/-!
# Absolute convergence of compact-test zero sums

Uniform Mellin decay on the critical strip is dominated by the regularized
multiplicity mass. Entire order-one growth supplies that mass, and the functional
equation and right-half-plane nonvanishing locate all zeros in the strip.
No critical-line hypothesis is needed.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- At a point in the closed critical strip, bounds for the test value
and for its squared-height multiple give a bound after multiplication by
one plus the squared complex norm. Use Re(rho)^2 <= 1 and the norm-square
identity. This converts vertical decay into the regular zero-mass majorant. -/
theorem normSq_weighted_test_bound (ρ : ℂ) (W : ℂ) (D₀ D₂ : ℝ) (hr : ρ.re ∈ Set.Icc (0 : ℝ) 1)
    (hW₀ : ‖W‖ ≤ D₀) (hW₂ : ρ.im ^ 2 * ‖W‖ ≤ D₂) : (1 + ‖ρ‖ ^ 2) * ‖W‖ ≤ 2 * D₀ + D₂ := by
  have hr₂ : ρ.re ^ 2 ≤ 1 := by
    have hh := pow_le_pow_left₀ hr.1 hr.2 2
    simpa only [one_pow] using hh
  have hnorm : ‖ρ‖ ^ 2 ≤ 1 + ρ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith only [hr₂]
  have hh := mul_le_mul_of_nonneg_right (add_le_add_left hnorm 1) (norm_nonneg W)
  nlinarith only [hh, hW₀, hW₂]

/-- If regular zero multiplicity mass is summable and all zeros lie in
the closed critical strip, the Mellin values of an even compactly supported
smooth logarithmic test are absolutely summable with analytic multiplicity.
Uniform bounds of orders zero and two dominate the terms by a constant
times regular zero mass; terms of zero multiplicity vanish.
This is the convergence step for the weighted zero side of the explicit formula. -/
theorem summable_mellin_zero_terms {F : ℂ → ℂ} (hm : Summable (regularZeroWeight F))
    (hs : ∀ ρ : ℂ, F ρ = 0 → ρ.re ∈ Set.Icc (0 : ℝ) 1) (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) := by
  obtain ⟨D₀, hD₀, h₀⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg 0 1 0
  obtain ⟨D₂, hD₂, h₂⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg 0 1 2
  apply Summable.of_norm_bounded (hm.mul_left (2 * D₀ + D₂))
  intro ρ
  by_cases hn : analyticOrderNatAt F ρ = 0
  · simp only [hn, Nat.cast_zero, zero_mul, norm_zero, regularZeroWeight, zero_div, mul_zero]
    exact le_refl (0 : ℝ)
  · have hr := hs ρ (apply_eq_zero_of_analyticOrderNatAt_ne_zero hn)
    have h₀' := h₀ ρ.re hr ρ.im
    have h₂' := h₂ ρ.re hr ρ.im
    rw [Complex.re_add_im, pow_zero, one_mul] at h₀'
    rw [Complex.re_add_im, sq_abs] at h₂'
    have hw := normSq_weighted_test_bound ρ _ D₀ D₂ hr h₀' h₂'
    have hp : 0 < 1 + ‖ρ‖ ^ 2 := by nlinarith only [sq_nonneg ‖ρ‖]
    have hdiv : ‖mellin (logarithmicTestWeight g) ρ‖ ≤ (2 * D₀ + D₂) / (1 + ‖ρ‖ ^ 2) := by
      apply (le_div_iff₀ hp).mpr
      exact (mul_comm _ _).trans_le hw
    rw [norm_mul, Complex.norm_natCast]
    calc
      _ ≤ (analyticOrderNatAt F ρ : ℝ) * ((2 * D₀ + D₂) / (1 + ‖ρ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg _)
      _ = (2 * D₀ + D₂) * regularZeroWeight F ρ := by
        unfold regularZeroWeight
        ring

/-- For an entire function nonzero at zero of order at most one, with a
conjugate functional equation and no zeros to the right of the critical strip,
the Mellin values of an even compactly supported smooth logarithmic test
form an absolutely summable family when weighted by analytic multiplicity.
Subquadratic growth gives summable regular zero mass, while reflection
locates the zeros in the strip. Apply the uniform Mellin decay comparison.
This removes independent zero-sum convergence assumptions from contour limits. -/
theorem summable_mellin_zero_terms_of_orderAtMostOne {F : ℂ → ℂ} {ε : ℂ} (hF : Differentiable ℂ F)
    (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (hε : ε ≠ 0)
    (hfe : ∀ s, F s = ε * star (F (1 - star s))) (hright : ∀ s, 1 < s.re → F s ≠ 0) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * mellin (logarithmicTestWeight g) ρ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_global_exponential_bound_of_orderAtMostOne hF.continuous horder (r := 3 / 2)
      (by norm_num only)
  exact
    summable_mellin_zero_terms
      (summable_regularZeroWeight hF h0 hC (by norm_num only : (0 : ℝ) ≤ 3 / 2)
        (by norm_num only : (3 / 2 : ℝ) < 2) hbound)
      (fun ρ hz ↦ zero_re_mem_Icc_of_functionalEquation hε hfe hright hz) g he hc hg

end PseudoPrime.AnalyticNumberTheory.General
