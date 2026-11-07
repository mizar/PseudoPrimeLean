/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDerivativeBounds

/-! # Summed sixth-order Poisson identity -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under individual RH, the completed-zero sixth-order resolvent series is
the same linear combination of the Poisson series and the two series of its
termwise derivatives. All three series are summable, so the pointwise identity
can be summed without changing multiplicities. Differentiation of the total
Poisson series remains a separate local-uniform convergence step. -/
theorem sixth_pole_zero_series_identity {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (8 * a ^ 5 / (a ^ 2 + ρ.im ^ 2) ^ 3)) =
      3 *
            (∑' ρ : ℂ,
              (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                (a / (a ^ 2 + ρ.im ^ 2))) -
          3 * a *
            (∑' ρ : ℂ,
              (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2)) +
        a ^ 2 *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3)) := by
  have h0 :=
    AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv ha
  have h1 := poisson_deriv_zero_summable hq hRH hp hne hinv ha
  have h2 := poisson_second_zero_summable hq hRH hp hne hinv ha
  have he (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (8 * a ^ 5 / (a ^ 2 + ρ.im ^ 2) ^ 3) =
      3 * ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a / (a ^ 2 + ρ.im ^ 2))) -
          (3 * a) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2)) +
        a ^ 2 *
          ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3)) := by
    rw [← sixth_pole_poisson_identity ha ρ.im]
    ring
  rw [tsum_congr he, ((h0.mul_left 3).sub (h1.mul_left (3 * a))).tsum_add (h2.mul_left (a ^ 2)),
    (h0.mul_left 3).tsum_sub (h1.mul_left (3 * a)), tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-- Under individual RH, eight times the actual refined-kernel zero mass is
the linear combination of the Poisson zero series at `27/25` and its two
termwise derivative series. The exact critical-line norm transfers the summed
sixth-pole identity without changing normalization or multiplicities. -/
theorem refined_six_pole_zero_identity {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      3 *
            (∑' ρ : ℂ,
              (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((27 / 25 : ℝ) / ((27 / 25 : ℝ) ^ 2 + ρ.im ^ 2))) -
          (3 * (27 / 25 : ℝ)) *
            (∑' ρ : ℂ,
              (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                ((ρ.im ^ 2 - (27 / 25 : ℝ) ^ 2) / ((27 / 25 : ℝ) ^ 2 + ρ.im ^ 2) ^ 2)) +
        (27 / 25 : ℝ) ^ 2 *
          (∑' ρ : ℂ,
            (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              (2 * (27 / 25 : ℝ) * ((27 / 25 : ℝ) ^ 2 - 3 * ρ.im ^ 2) /
                ((27 / 25 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3)) := by
  have h := sixth_pole_zero_series_identity hq hRH hp hne hinv (a := 27 / 25) (by norm_num only)
  have he :
    8 *
        (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖refinedSixPoleKernel.function (Complex.I * ρ.im)‖) =
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (8 * (27 / 25 : ℝ) ^ 5 / ((27 / 25 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ρ
    rw [refined_six_pole_norm]
    ring
  exact he.trans h

end PseudoPrime.PrimeTestBounds.MillerRabin
