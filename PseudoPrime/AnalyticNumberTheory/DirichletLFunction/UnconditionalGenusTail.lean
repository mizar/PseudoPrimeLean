/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalGenusTailKernel

/-! # Uniform unconditional high-genus correction bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character of modulus at least two and with
nonprincipal inverse, the shifted inverse-square mass at three halves has the
explicit logarithmic modulus bound displayed below. Specialize the existing
unconditional genus estimate to shift one half and height zero. Both constants
are fixed independently of the modulus. -/
theorem completed_genus_three_halves_mass_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖(((3 / 2 : ℝ) : ℂ) - ρ)⁻¹‖ ^ 2) ≤
      2 *
        (12 + LogFreeDensity.completedGenusMassShiftConstant * (Real.log 4 + 1) + Real.log q +
          LogFreeDensity.completedGenusMassCenterConstant * (Real.log 4 + 1)) := by
  obtain ⟨A, B, hA, hB, _, _, hb⟩ :=
    LogFreeDensity.exists_completed_genus_inverse_square_mass_le_uniform_bound hq hne hp hinv (η :=
      1 / 2) (by norm_num only) le_rfl 0
  rw [hA, hB] at hb
  norm_num only [Complex.ofReal_zero, mul_zero, add_zero, abs_zero] at hb
  linarith only [hb]

/-- For a primitive nonprincipal character with nonprincipal inverse and modulus
at least two, any genus tail starting at absolute height at least one is bounded
by sixteen times the full shifted mass. Bound finite sums pointwise and use
summability of the nonnegative shifted mass. This retains actual multiplicities
and applies without RH or quantitative zero exclusion. -/
theorem tsum_norm_completed_genus_tail_le_shifted_mass {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) :
    (∑' ρ : ℂ,
        if R ≤ |ρ.im| then
          ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
        else 0) ≤
      16 *
        ∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖(((3 / 2 : ℝ) : ℂ) - ρ)⁻¹‖ ^ 2 := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) :
    0 ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖(((3 / 2 : ℝ) : ℂ) - ρ)⁻¹‖ ^ 2 :=
    mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ) (sq_nonneg _)
  have hs :=
    LogFreeDensity.summable_completed_genus_inverse_square hq hne hp hinv (s := ((3 / 2 : ℝ) : ℂ))
      (by norm_num only [Complex.ofReal_re])
  apply Real.tsum_le_of_sum_le (fun ρ ↦ ite_nonneg (norm_nonneg _) le_rfl)
  intro S
  have hf := hs.sum_le_tsum S (fun ρ _ ↦ hn ρ)
  have ht :
    (∑ ρ ∈ S,
        if R ≤ |ρ.im| then
          ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
        else 0) ≤
      16 *
        ∑ ρ ∈ S,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖(((3 / 2 : ℝ) : ℂ) - ρ)⁻¹‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ _
    by_cases hh : R ≤ |ρ.im|
    · rw [ite_eq_left hh]
      simpa only [mul_assoc] using
        norm_completed_genus_term_le_shifted_mass_of_large_im hp hne hinv (hR.trans hh)
    · rw [ite_eq_right hh]
      exact mul_nonneg (by norm_num only) (hn ρ)
  exact ht.trans (mul_le_mul_of_nonneg_left hf (by norm_num only))

/-- For a primitive nonprincipal character with nonprincipal inverse and modulus
at least two, every high genus tail has a uniform bound of size `O(log q)` with
the two fixed constants displayed below. Combine the tail-to-mass comparison
with the explicit shifted bound. The bound is independent of the tail cutoff
and supplies the correction term in the regularized explicit-formula budget. -/
theorem tsum_norm_completed_genus_tail_le_uniform_bound {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) :
    (∑' ρ : ℂ,
        if R ≤ |ρ.im| then
          ‖(MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
              (1 / ((2 : ℂ) - ρ) + 1 / ρ)‖
        else 0) ≤
      32 *
        (12 + LogFreeDensity.completedGenusMassShiftConstant * (Real.log 4 + 1) + Real.log q +
          LogFreeDensity.completedGenusMassCenterConstant * (Real.log 4 + 1)) := by
  have ht := tsum_norm_completed_genus_tail_le_shifted_mass hq hp hne hinv hR
  have hm := completed_genus_three_halves_mass_le_explicit hq hp hne hinv
  linarith only [ht, hm]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
