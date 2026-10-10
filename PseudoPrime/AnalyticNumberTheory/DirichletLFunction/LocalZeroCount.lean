/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum

/-!
# Uniform local counts of completed Dirichlet zeros

Individual RH and the Poisson zero identity bound multiplicity in height windows
by log q and a logarithmic height error, uniformly in the primitive character.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under individual RH for a primitive nonprincipal character, every divisor multiplicity
in the height window |Im rho - t| <= 1 is at most twice its Poisson weight centered at
3/2 + i t. The critical-line real part makes the denominator lie between one and two;
analyticity makes multiplicities nonnegative. This converts Poisson mass to local zero counts. -/
theorem completed_divisor_le_two_mul_poisson {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {t : ℝ} {ρ : ℂ} (ht : |ρ.im - t| ≤ 1) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      2 *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (1 / Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ))) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · change (D : ℝ) ≤ 2 * ((D : ℝ) * _)
    simp only [hD, Int.cast_zero, zero_mul, mul_zero, le_refl]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    have hn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have he : Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) = 1 + (t - ρ.im) ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
        Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, one_mul, hr]
      ring
    have hd : 0 < Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) := by
      rw [he]
      nlinarith only [sq_nonneg (t - ρ.im)]
    have hupper : Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) ≤ 2 := by
      rw [he]
      have hu := (abs_le.mp ht).2
      have hl := (abs_le.mp ht).1
      nlinarith only [hu, hl, sq_nonneg (t - ρ.im)]
    have hratio : (1 : ℝ) ≤ 2 / Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) :=
      (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hupper)
    have hb := mul_le_mul_of_nonneg_left hratio hn
    change (D : ℝ) ≤ 2 * ((D : ℝ) * _)
    convert hb using 1 <;> ring

/-- A primitive nonprincipal character of modulus q >= 2 satisfying individual RH has,
in every height window of radius one, finite zero multiplicity bounded by log q plus a
logarithmic height error. The positive error constant is uniform in q and the character.
Compare each multiplicity with twice its Poisson weight, bound the finite sum by the
convergent full series, and use the uniform completed logarithmic-derivative estimate.
This supplies local zero counts for tails of quadratically decaying kernel sums. -/
theorem exists_uniform_local_zeroMultiplicity_bound :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              GRH.DirichletRiemannHypothesis χ →
                χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (t : ℝ) (S : Finset ℂ),
                  (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
                    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
                      Real.log q + 2 * A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨A, hA, hb⟩ :=
    exists_uniform_poissonSum_error_le_log (show (1 : ℝ) < 3 / 2 by norm_num only)
      (show (3 / 2 : ℝ) ≤ 2 by norm_num only)
  refine ⟨A, hA, ?_⟩
  intro q _ hq χ hRH hp hne hinv t S hS
  let P : ℂ → ℝ := fun ρ ↦
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      (1 / Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ))
  have hr : (((3 / 2 : ℝ) : ℂ) + Complex.I * t).re = 3 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs : 1 / 2 < (((3 / 2 : ℝ) : ℂ) + Complex.I * t).re := by
    rw [hr]
    norm_num only
  have hps := summable_completed_poisson_terms hq hRH hp hne hinv hs
  rw [hr, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num only] at hps
  have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn : ∀ ρ : ℂ, 0 ≤ P ρ := fun ρ ↦
    mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ)
      (div_nonneg zero_le_one (Complex.normSq_nonneg _))
  have hf :
    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤ 2 * ∑ ρ ∈ S, P ρ := by
    rw [Finset.mul_sum]
    exact
      Finset.sum_le_sum (fun ρ hρ ↦ completed_divisor_le_two_mul_poisson hRH hp hne hinv (hS ρ hρ))
  have hfinite : ∑ ρ ∈ S, P ρ ≤ ∑' ρ, P ρ := hps.sum_le_tsum S (fun ρ _ ↦ hn ρ)
  have he := hb q hq χ hRH hp hne hinv t
  rw [show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num only] at he
  have hu := (abs_le.mp he).2
  calc
    _ ≤ 2 * ∑ ρ ∈ S, P ρ := hf
    _ ≤ 2 * ∑' ρ, P ρ := mul_le_mul_of_nonneg_left hfinite (by norm_num only)
    _ ≤ _ := by
      change (∑' ρ, P ρ) - Real.log q / 2 ≤ A * (Real.log (4 + |t|) + 1) at hu
      linarith only [hu]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
