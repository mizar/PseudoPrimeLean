/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDerivativeBounds
public import Mathlib.Analysis.Calculus.SmoothSeries

/-! # Local differentiation of the completed Poisson zero sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A summable anchor with nonnegative weights permits the first Poisson differentiation.
The anchor sum supplies the majorant. -/
theorem hasDerivAt_poisson_sum {m : ℂ → ℝ} {a : ℝ} (ha : 0 < a) (hn : ∀ ρ, 0 ≤ m ρ)
    (hs : Summable (fun ρ : ℂ ↦ m ρ * (a / (a ^ 2 + ρ.im ^ 2)))) :
    HasDerivAt (fun u : ℝ ↦ ∑' ρ : ℂ, m ρ * (u / (u ^ 2 + ρ.im ^ 2)))
      (∑' ρ : ℂ, m ρ * ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2)) a := by
  let U : Set ℝ := Set.Ioi (a / 2)
  have hg :
    ∀ ρ : ℂ,
      ∀ u ∈ U,
        HasDerivAt (fun v : ℝ ↦ m ρ * (v / (v ^ 2 + ρ.im ^ 2)))
          (m ρ * ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2)) u := by
    intro ρ u hu
    change a / 2 < u at hu
    exact (hasDerivAt_poisson_distance (by linarith only [ha, hu] : 0 < u) ρ.im).const_mul _
  have hb :
    ∀ ρ : ℂ,
      ∀ u ∈ U,
        ‖m ρ * ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2)‖ ≤
          (4 / a) * (m ρ * (a / (a ^ 2 + ρ.im ^ 2))) := by
    intro ρ u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn ρ)]
    have he : (4 / a) * (m ρ * (a / (a ^ 2 + ρ.im ^ 2))) = m ρ * (4 / (a ^ 2 + ρ.im ^ 2)) := by
      calc
        _ = ((4 / a) * a) * (m ρ / (a ^ 2 + ρ.im ^ 2)) := by ring
        _ = _ := by
          rw [div_mul_cancel₀ _ ha.ne']; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (poisson_deriv_uniform_le ha (le_of_lt hu) ρ.im) (hn ρ)
  have haU : a ∈ U := by
    change a / 2 < a; linarith only [ha]
  exact
    hasDerivAt_tsum_of_isPreconnected (hs.mul_left (4 / a)) isOpen_Ioi
      (convex_Ioi (a / 2)).isPreconnected hg hb haU hs haU

/-- Under individual RH, the completed-zero Poisson series is differentiable
at every positive pole distance and its derivative is the sum of termwise
derivatives. A summable Poisson majorant controls all derivatives on the
half-line above half the chosen distance. This is the first differentiation
step needed for the refined sixth-pole zero identity. -/
theorem hasDerivAt_completed_poisson_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    HasDerivAt
      (fun u : ℝ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (u / (u ^ 2 + ρ.im ^ 2)))
      (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2))
      a := by
  have hA : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA ρ
  exact
    hasDerivAt_poisson_sum ha hn
      (AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv
        ha)

/-- A summable anchor with nonnegative weights permits the second Poisson differentiation.
The anchor sum supplies the majorant. -/
theorem hasDerivAt_poisson_deriv_sum {m : ℂ → ℝ} {a : ℝ} (ha : 0 < a) (hn : ∀ ρ, 0 ≤ m ρ)
    (hs : Summable (fun ρ : ℂ ↦ m ρ * (a / (a ^ 2 + ρ.im ^ 2)))) :
    HasDerivAt (fun u : ℝ ↦ ∑' ρ : ℂ, m ρ * ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2))
      (∑' ρ : ℂ, m ρ * (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3)) a := by
  let U : Set ℝ := Set.Ioi (a / 2)
  have hbase := poisson_deriv_summable ha hn hs
  have hg :
    ∀ ρ : ℂ,
      ∀ u ∈ U,
        HasDerivAt (fun v : ℝ ↦ m ρ * ((ρ.im ^ 2 - v ^ 2) / (v ^ 2 + ρ.im ^ 2) ^ 2))
          (m ρ * (2 * u * (u ^ 2 - 3 * ρ.im ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 3)) u := by
    intro ρ u hu
    change a / 2 < u at hu
    exact (hasDerivAt_poisson_distance_deriv (by linarith only [ha, hu] : 0 < u) ρ.im).const_mul _
  have hb :
    ∀ ρ : ℂ,
      ∀ u ∈ U,
        ‖m ρ * (2 * u * (u ^ 2 - 3 * ρ.im ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 3)‖ ≤
          (48 / a ^ 2) * (m ρ * (a / (a ^ 2 + ρ.im ^ 2))) := by
    intro ρ u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn ρ)]
    have he :
      (48 / a ^ 2) * (m ρ * (a / (a ^ 2 + ρ.im ^ 2))) = m ρ * (48 / (a * (a ^ 2 + ρ.im ^ 2))) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      have hc : (a⁻¹) ^ 2 * a = a⁻¹ := by
        calc
          (a⁻¹) ^ 2 * a = a⁻¹ * (a⁻¹ * a) := by ring
          _ = _ := by rw [inv_mul_cancel₀ ha.ne', mul_one]
      calc
        _ = 48 * m ρ * (a ^ 2 + ρ.im ^ 2)⁻¹ * ((a⁻¹) ^ 2 * a) := by ring
        _ = _ := by
          rw [hc]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (poisson_second_uniform_le ha (le_of_lt hu) ρ.im) (hn ρ)
  have haU : a ∈ U := by
    change a / 2 < a; linarith only [ha]
  exact
    hasDerivAt_tsum_of_isPreconnected (hs.mul_left (48 / a ^ 2)) isOpen_Ioi
      (convex_Ioi (a / 2)).isPreconnected hg hb haU hbase haU

/-- Under individual RH, the series of first Poisson-distance derivatives is
differentiable at every positive distance, with derivative given by the series
of second derivatives. A single anchor Poisson series provides a summable
local-uniform majorant. This completes termwise differentiation through order two. -/
theorem hasDerivAt_completed_poisson_deriv_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    HasDerivAt
      (fun u : ℝ ↦
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2))
      (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3))
      a := by
  have hA : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hA ρ
  exact
    hasDerivAt_poisson_deriv_sum ha hn
      (AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv
        ha)

end PseudoPrime.PrimeTestBounds.MillerRabin
