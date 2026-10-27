/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting

/-! # Unconditional inverse-square mass of completed Dirichlet zeros -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character with nonprincipal inverse, divisor
multiplicities divided by squared zero norms form a summable family without RH.
Split at norm one: the inner part has finite support, and the outer part is
bounded by twice the existing summable zero weight. This supplies a finite
character-dependent mass for unconditional contour estimates. -/
theorem summable_divisor_div_normSq_unconditionally {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ) := by
  classical
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ
  let f := fun ρ : ℂ ↦ (D ρ : ℝ) / Complex.normSq ρ
  let near := fun ρ : ℂ ↦ if ‖ρ‖ ≤ 1 then f ρ else 0
  let far := fun ρ : ℂ ↦ if ‖ρ‖ ≤ 1 then 0 else f ρ
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hD (ρ : ℂ) : 0 ≤ (D ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hf (ρ : ℂ) : 0 ≤ f ρ := div_nonneg (hD ρ) (Complex.normSq_nonneg _)
  have hfinite : Function.HasFiniteSupport near := by
    apply (finite_dirichletCompletedLFunction_zerosOn χ hne (isCompact_closedBall (0 : ℂ) 1)).subset
    intro ρ hρ
    have hnear : near ρ ≠ 0 := Function.mem_support.mp hρ
    have hnorm : ‖ρ‖ ≤ 1 := by
      by_contra h
      exact hnear (ite_eq_right h)
    have hDv : D ρ ≠ 0 := by
      intro h
      apply hnear
      simp only [near, ite_eq_left hnorm, f, h, Int.cast_zero, zero_div]
    exact
      ⟨by simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm,
        dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hDv⟩
  have hfarNonneg (ρ : ℂ) : 0 ≤ far ρ := by
    dsimp only [far]
    split
    · exact le_refl 0
    · exact hf ρ
  have hfarBound (ρ : ℂ) : far ρ ≤ 2 * completedLFunctionZeroWeight χ ρ := by
    by_cases hnorm : ‖ρ‖ ≤ 1
    · simpa only [far, ite_eq_left hnorm] using
        mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (completedLFunctionZeroWeight_nonneg hne ρ)
    · have hx : 1 ≤ ‖ρ‖ ^ 2 := one_le_pow₀ (le_of_lt (lt_of_not_ge hnorm))
      have hxpos : 0 < ‖ρ‖ ^ 2 := zero_lt_one.trans_le hx
      have hden : 0 < 1 + ‖ρ‖ ^ 2 := by linarith only [hx]
      have hmult := mul_le_mul_of_nonneg_left hx (hD ρ)
      dsimp only [far, f, completedLFunctionZeroWeight]
      rw [ite_eq_right hnorm, Complex.normSq_eq_norm_sq, ← mul_div_assoc]
      exact (div_le_div_iff₀ hxpos hden).mpr (by nlinarith only [hmult])
  have hsumfar : Summable far :=
    Summable.of_nonneg_of_le hfarNonneg hfarBound
      ((summable_completedLFunctionZeroWeight hq hp hne hinv).mul_left 2)
  have heq : (fun ρ ↦ near ρ + far ρ) = f := by
    funext ρ
    dsimp only [near, far]
    split <;> simp only [add_zero, zero_add]
  change Summable f
  rw [← heq]
  exact (summable_of_hasFiniteSupport hfinite).add hsumfar

/-- For a completed Dirichlet function, sum the analytic divisor multiplicities divided
by the squared zero norms, with the usual totalized value at zero. For primitive
nonprincipal characters this is finite without RH. This constant replaces the
RH-specific closed-form mass in horizontal contour estimates. -/
noncomputable def completedLFunctionInverseSquareMass {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ

/-- The inverse-square mass of a nonprincipal completed function is nonnegative.
Entirety makes each divisor multiplicity nonnegative. This permits Cauchy--Schwarz
and monotonicity estimates using the mass as a fixed character-dependent constant. -/
theorem completedLFunctionInverseSquareMass_nonneg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hne : χ ≠ 1) : 0 ≤ completedLFunctionInverseSquareMass χ := by
  apply tsum_nonneg
  intro ρ
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  exact
    div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ)
      (Complex.normSq_nonneg _)

/-- For a primitive nonprincipal character, every finite inverse-square divisor sum
restricted to a ball is at most the full inverse-square mass. Compare the ball and
global divisors and use unconditional summability. This controls the first factor
in the truncated-genus Cauchy--Schwarz estimate. -/
theorem sum_divisor_ball_div_normSq_le_inverseSquareMass {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (R : ℝ)
    (S : Finset ℂ) :
    (∑ ρ ∈ S,
        (MeromorphicOn.divisor χ.completedLFunction (Metric.ball (0 : ℂ) R) ρ : ℝ) / ‖ρ‖ ^ 2) ≤
      completedLFunctionInverseSquareMass χ := by
  classical
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hnonneg (ρ : ℂ) :
    0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ :=
    div_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ)
      (Complex.normSq_nonneg _)
  have hpoint (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction (Metric.ball (0 : ℂ) R) ρ : ℝ) / ‖ρ‖ ^ 2 ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) / Complex.normSq ρ := by
    rw [divisor_ball_eq_if_univ hne ρ]
    split
    · rw [Complex.normSq_eq_norm_sq]
    · simpa only [Int.cast_zero, zero_div] using hnonneg ρ
  exact
    (Finset.sum_le_sum (fun ρ _ ↦ hpoint ρ)).trans
      ((summable_divisor_div_normSq_unconditionally hq hp hne hinv).sum_le_tsum S
        (fun ρ _ ↦ hnonneg ρ))

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
