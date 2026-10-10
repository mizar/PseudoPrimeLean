/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CenteredHadamard
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedVerticalGrowth

/-!
# Poisson-weighted completed Dirichlet zero sums

The real Hadamard identity identifies shifted Poisson zero mass with the completed
logarithmic derivative and isolates the conductor term log q / 2.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character satisfying individual RH, the real part of each
divisor-weighted genus term splits into its shifted Poisson weight and inverse-zero term.
Nonzero multiplicity forces Re rho = 1/2; the complex inverse formula then gives the equality.
This pointwise identity separates the centered Hadamard series into two convergent real masses. -/
theorem completed_genusTerm_re_eq_poisson_add_inverse {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (s ρ : ℂ) :
    ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
          (1 / (s - ρ) + 1 / ρ)).re =
      (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) *
        ((s.re - 1 / 2) / Complex.normSq (s - ρ) + (1 / ρ).re) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
  by_cases hD : D = 0
  · change ((D : ℂ) * _).re = (D : ℝ) * _
    simp only [hD, Int.cast_zero, zero_mul, Complex.zero_re]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    change ((D : ℂ) * _).re = (D : ℝ) * _
    rw [← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.add_re, one_div (s - ρ),
      Complex.inv_re, Complex.sub_re, hr]

/-- For a primitive nonprincipal character satisfying individual RH, the real inverse-zero
term equals half the inverse-square divisor mass. Zero multiplicities vanish; at each zero,
Re rho = 1/2 identifies the real part of its inverse. This supplies a summable central mass. -/
theorem completed_inverseTerm_eq_half_inverseSquare {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (ρ : ℂ) :
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) * (1 / ρ).re =
      (1 / 2 : ℝ) *
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) /
          Complex.normSq ρ) := by
  let D := MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ
  by_cases hD : D = 0
  · change (D : ℝ) * _ = _ * ((D : ℝ) / _)
    simp only [hD, Int.cast_zero, zero_mul, zero_div, mul_zero]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    rw [one_div ρ, Complex.inv_re, hr]
    ring

/-- Under individual RH, a primitive nonprincipal character of modulus at least two with
nonprincipal inverse has a summable Poisson zero series at every Re s > 1/2.
Subtract the convergent inverse-zero mass from the real genus-one series.
This justifies finite-sum comparisons and integration of conductor-normalized zero masses. -/
theorem summable_completed_poisson_terms {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((s.re - 1 / 2) / Complex.normSq (s - ρ))) := by
  have hz :=
    ((summable_divisor_div_normSq_of_dirichletRH hq hRH hp hne hinv).mul_left (1 / 2 : ℝ)).congr
      (fun ρ ↦ (completed_inverseTerm_eq_half_inverseSquare hRH hp hne hinv ρ).symm)
  have hg := Complex.reCLM.summable (summable_completed_genus_terms hq hRH hp hne hinv hs)
  apply (hg.sub hz).congr
  intro ρ
  rw [Complex.reCLM_apply, completed_genusTerm_re_eq_poisson_add_inverse hRH hp hne hinv]
  rw [mul_add, add_sub_cancel_right]

/-- For modulus at least two, a primitive nonprincipal character with nonprincipal inverse
and individual RH has Poisson zero mass at Re s > 1/2 equal to the real completed logarithmic
derivative plus log q / 2. Take real parts of the convergent centered Hadamard identity,
then cancel the inverse-zero mass using the functional-equation Hadamard constant.
The identity isolates the conductor coefficient needed for sharp Mellin-kernel mass estimates. -/
theorem completed_poissonSum_eq_logDeriv_re {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : 1 / 2 < s.re) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ) *
          ((s.re - 1 / 2) / Complex.normSq (s - ρ))) =
      (logDeriv (DirichletCharacter.completedLFunction χ) s).re + Real.log q / 2 := by
  let D : ℂ → ℝ := fun ρ ↦
    (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℝ)
  let P : ℂ → ℝ := fun ρ ↦ D ρ * ((s.re - 1 / 2) / Complex.normSq (s - ρ))
  let Z : ℂ → ℝ := fun ρ ↦ D ρ * (1 / ρ).re
  have hz : Summable Z :=
    ((summable_divisor_div_normSq_of_dirichletRH hq hRH hp hne hinv).mul_left (1 / 2 : ℝ)).congr
      (fun ρ ↦ (completed_inverseTerm_eq_half_inverseSquare hRH hp hne hinv ρ).symm)
  have he :
    ∀ ρ : ℂ,
      Complex.reCLM
          ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ ρ : ℂ) *
            (1 / (s - ρ) + 1 / ρ)) =
        P ρ + Z ρ :=
    fun ρ ↦ by
    rw [Complex.reCLM_apply, completed_genusTerm_re_eq_poisson_add_inverse hRH hp hne hinv]
    change D ρ * (_ + _) = D ρ * _ + D ρ * _
    exact mul_add _ _ _
  have hps : Summable P := summable_completed_poisson_terms hq hRH hp hne hinv hs
  have hi := congrArg Complex.reCLM (completed_centered_logDeriv_eq_genusSum hq hRH hp hne hinv hs)
  rw [map_sub, Complex.reCLM.map_tsum (summable_completed_genus_terms hq hRH hp hne hinv hs),
    tsum_congr he, hps.tsum_add hz] at hi
  have hb := primitiveBRe_eq_neg_zeroMass_of_dirichletRH hq hRH hp hne hinv
  rw [primitiveBRe, (hp : χ.conductor = q)] at hb
  change (∑' ρ, P ρ) = _
  change
    (logDeriv (DirichletCharacter.completedLFunction χ) 0).re + (1 / 2) * Real.log q =
      -(∑' ρ, Z ρ) at hb
  simp only [Complex.reCLM_apply] at hi
  linarith only [hi, hb]

/-- At every fixed real part in (1,2], the Poisson zero mass of a primitive nonprincipal
character satisfying individual RH differs from log q / 2 by a logarithmic height bound.
The positive constant is independent of the modulus and character. Substitute the real
Hadamard identity and apply the uniform completed logarithmic-derivative estimate.
This is the conductor-uniform resolvent input for sharp kernel-mass asymptotics. -/
theorem exists_uniform_poissonSum_error_le_log {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ t : ℝ,
                  |(∑' ρ : ℂ,
                          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
                            ((σ - 1 / 2) / Complex.normSq (((σ : ℂ) + Complex.I * t) - ρ))) -
                        Real.log q / 2| ≤
                    A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨A, hA, hb⟩ := exists_uniform_norm_completed_vertical_right_le_log hσ hσ'
  refine ⟨A, hA, ?_⟩
  intro q _ hq χ hRH hp hne hinv t
  have hr : ((σ : ℂ) + Complex.I * t).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs : 1 / 2 < ((σ : ℂ) + Complex.I * t).re := by
    rw [hr]
    linarith only [hσ]
  have he := completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv hs
  rw [hr] at he
  rw [he, add_sub_cancel_right]
  exact (Complex.abs_re_le_norm _).trans (hb q χ hne t)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
