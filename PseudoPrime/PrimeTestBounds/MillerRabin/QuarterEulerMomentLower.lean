/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerSmoothed
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsi1000Upper

/-! # Lower moment bounds beyond the certified Euler prefix -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, each of the first three Mangoldt moments between 1000 and `b`
is bounded below by a boundary correction and an explicit power-log integral.
The Chebyshev error is at most the three-quarter power throughout the interval. -/
theorem quarter_euler_moment_lower (hRH : RiemannHypothesis) {k : ℕ} (hk : k ≤ 2) {b : ℝ}
    (hb : (1000 : ℝ) ≤ b) :
    -((1000 : ℝ) ^ (3 / 4 : ℝ)) *
          AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 1000 +
        (∫ t in Set.Ioc (1000 : ℝ) b,
          (1 - (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
            AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k t) ≤
      ∑ n ∈ Finset.Ioc ⌊(1000 : ℝ)⌋₊ ⌊b⌋₊, quarterMangoldtMoment k n := by
  let E : ℝ → ℝ := fun t ↦ t - t ^ (3 / 4 : ℝ)
  let D : ℝ → ℝ := fun t ↦ 1 - (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))
  have hE : ∀ t ∈ Set.Icc (1000 : ℝ) b, HasDerivAt E (D t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith only [ht.1]
    have h := (hasDerivAt_id t).sub (Real.hasDerivAt_rpow_const (p := (3 / 4 : ℝ)) (Or.inl ht0.ne'))
    change
      HasDerivAt (fun z : ℝ ↦ z - z ^ (3 / 4 : ℝ)) (1 - (3 / 4 : ℝ) * t ^ ((3 / 4 : ℝ) - 1)) t at h
    dsimp only [E, D]
    norm_num only at h ⊢
    exact h
  have hD : ContinuousOn D (Set.Icc 1000 b) := by
    intro t ht
    have ht0 : 0 < t := by linarith only [ht.1]
    exact
      (continuousAt_const.sub
          (continuousAt_const.mul
            (Real.continuousAt_rpow_const t (-(1 / 4 : ℝ)) (Or.inl ht0.ne')))).continuousWithinAt
  have hψ : ∀ t ∈ Set.Icc (1000 : ℝ) b, E t ≤ Chebyshev.psi t := by
    intro t ht
    have ht0 : 0 ≤ t := by linarith only [ht.1]
    have h :=
      (abs_le.mp (LLS.psi_error_quarter_sqrt hRH (show (625 : ℝ) ≤ t by linarith only [ht.1]))).1
    rw [quarter_sqrt_product ht0] at h
    dsimp only [E]
    linarith only [h]
  have hd :
    ∀ t ∈ Set.Icc (1000 : ℝ) b,
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (79 / 50) k t ≤ 0 := by
    intro t ht
    have hlog := Real.log_le_log (show (0 : ℝ) < 1000 by norm_num only) ht.1
    have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    apply
      AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos k (by norm_num only)
        (by linarith only [ht.1])
    nlinarith only [refined_log_1000_lower, hlog, hk']
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_moment_tail_lower_integral (79 / 50) k
      (show (1 : ℝ) ≤ 1000 by norm_num only) hb E D hE hD hψ hd
  have hw : 0 ≤ AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 1000 := by
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    positivity
  have hc :=
    mul_le_mul_of_nonneg_left
      (show -((1000 : ℝ) ^ (3 / 4 : ℝ)) ≤ E 1000 - Chebyshev.psi 1000
        by
        dsimp only [E]
        linarith only [quarter_psi1000_upper])
      hw
  dsimp only [E, D] at h
  have ht :
    (∑ n ∈ Finset.Ioc ⌊(1000 : ℝ)⌋₊ ⌊b⌋₊,
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k n *
          ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc ⌊(1000 : ℝ)⌋₊ ⌊b⌋₊, quarterMangoldtMoment k n := by
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [quarterMangoldtMoment, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    ring
  rw [ht] at h
  linarith only [h, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
