/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ChebyshevQuarterError
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel

/-! Chebyshev quarter-power error for Euler moment tails. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH and above 625, Chebyshev psi differs from its main term by at most the
three-quarter power. Rewrite the established repeated-square-root estimate. -/
theorem quarter_psi_error_rpow (hRH : RiemannHypothesis) {t : ℝ} (ht : 625 ≤ t) :
    |Chebyshev.psi t - t| ≤ t ^ (3 / 4 : ℝ) := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  have he : Real.sqrt t * Real.sqrt (Real.sqrt t) = t ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul ht0, ←
      Real.rpow_add (by linarith only [ht] : 0 < t)]
    norm_num only
  rw [← he]
  exact LLS.psi_error_quarter_sqrt hRH ht

/-- Under RH, a decreasing power-log Mangoldt moment has a finite-tail upper bound using the
Chebyshev envelope `t + t^(3/4)`. The lower endpoint keeps its exact psi value. -/
theorem quarter_moment_tail_upper (hRH : RiemannHypothesis) (σ : ℝ) (k : ℕ) {a b : ℝ} (ha : 625 ≤ a)
    (hab : a ≤ b) (hσ : 0 ≤ σ) (hk : ∀ t ∈ Set.Icc a b, (k : ℝ) ≤ σ * Real.log t) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k n *
          ArithmeticFunction.vonMangoldt n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k b * (b + b ^ (3 / 4 : ℝ)) -
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k a * Chebyshev.psi a -
        ∫ t in Set.Ioc a b,
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv σ k t *
            (t + t ^ (3 / 4 : ℝ)) := by
  apply
    AnalyticNumberTheory.Arithmetic.mangoldt_moment_tail_upper σ k (by linarith only [ha]) hab
      (fun t ↦ t + t ^ (3 / 4 : ℝ))
  · apply ContinuousOn.add continuousOn_id
    intro t ht
    have ht0 : 0 < t := by linarith only [ha, ht.1]
    exact (Real.continuousAt_rpow_const t (3 / 4 : ℝ) (Or.inl ht0.ne')).continuousWithinAt
  · intro t ht
    have ht625 : 625 ≤ t := ha.trans ht.1
    have h := (abs_le.mp (quarter_psi_error_rpow hRH ht625)).2
    linarith only [h]
  · intro t ht
    exact
      AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos k hσ
        (by linarith only [ha, ht.1]) (hk t ht)

/-- Integrating the quarter-power Chebyshev envelope by parts replaces the upper endpoint
an explicit tail integral while retaining the cutoff correction. This prepares the infinite
limit. -/
theorem quarter_moment_tail_envelope (hRH : RiemannHypothesis) (σ : ℝ) (k : ℕ) {a b : ℝ}
    (ha : 625 ≤ a) (hab : a ≤ b) (hσ : 0 ≤ σ) (hk : ∀ t ∈ Set.Icc a b, (k : ℝ) ≤ σ * Real.log t) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k n *
          ArithmeticFunction.vonMangoldt n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k a *
          (a + a ^ (3 / 4 : ℝ) - Chebyshev.psi a) +
        ∫ t in Set.Ioc a b,
          (1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
            AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight σ k t := by
  apply
    AnalyticNumberTheory.Arithmetic.mangoldt_moment_tail_upper_integral σ k (by linarith only [ha])
      hab (fun t ↦ t + t ^ (3 / 4 : ℝ)) (fun t ↦ 1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)))
  · intro t ht
    have ht0 : 0 < t := by linarith only [ha, ht.1]
    have h := (hasDerivAt_id t).add (Real.hasDerivAt_rpow_const (p := (3 / 4 : ℝ)) (Or.inl ht0.ne'))
    convert h using 1
    · rfl
    · congr 2
      norm_num only
  · apply ContinuousOn.add continuousOn_const
    apply ContinuousOn.const_mul
    intro t ht
    have ht0 : 0 < t := by linarith only [ha, ht.1]
    exact (Real.continuousAt_rpow_const t (-(1 / 4 : ℝ)) (Or.inl ht0.ne')).continuousWithinAt
  · intro t ht
    have h := (abs_le.mp (quarter_psi_error_rpow hRH (ha.trans ht.1))).2
    linarith only [h]
  · intro t ht
    exact
      AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos k hσ
        (by linarith only [ha, ht.1]) (hk t ht)

end PseudoPrime.PrimeTestBounds.MillerRabin
