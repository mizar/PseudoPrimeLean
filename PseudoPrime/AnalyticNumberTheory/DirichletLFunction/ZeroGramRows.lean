/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum
public import PseudoPrime.Analysis.ExponentialMeanSquareSchur

/-!
# Exact Gram rows of completed Dirichlet zeros

Individual RH matches the Laplace Gram width with the Poisson identity at real part 5/2.
The conductor term is retained exactly, without the general reflected-profile factor nine.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For primitive nonprincipal individual RH data, a Gram row term is twice its actual
Poisson term at 5/2+iT. Nonzero multiplicity locates the zero on the critical line.
Zero multiplicity makes both sides vanish without a location assumption. -/
theorem completed_gram_term_eq_poisson {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (T : ℝ) (ρ : ℂ) :
    (analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
        PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (T - ρ.im) =
      2 *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (2 / Complex.normSq ((((5 / 2 : ℝ) : ℂ) + T * Complex.I) - ρ))) := by
  rw [completed_divisor_eq_analyticOrderNatAt hne, Int.cast_natCast]
  by_cases hz : χ.completedLFunction ρ = 0
  · have hr := completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv hz
    have hd : Complex.normSq ((((5 / 2 : ℝ) : ℂ) + T * Complex.I) - ρ) = 4 + (T - ρ.im) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero,
        add_zero, hr, Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add]
      ring
    rw [hd, PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel]
    ring
  · have ho : analyticOrderNatAt χ.completedLFunction ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
    simp only [ho, Nat.cast_zero, zero_mul, mul_zero]

/-- The actual completed-zero Gram row is summable and equals log q plus twice the
real completed logarithmic derivative at 5/2+iT. Use the exactly matching Poisson width.
This supplies the conductor normalization for a fixed character. -/
theorem completed_gram_row_sum {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (T : ℝ) :
    Summable
        (fun ρ : ℂ ↦
          (analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
            PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (T - ρ.im)) ∧
      (∑' ρ : ℂ,
          (analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
            PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (T - ρ.im)) =
        Real.log q +
          2 * (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + T * Complex.I)).re := by
  have hr : ((((5 / 2 : ℝ) : ℂ) + T * Complex.I)).re = 5 / 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hs : 1 / 2 < ((((5 / 2 : ℝ) : ℂ) + T * Complex.I)).re := by
    rw [hr]
    norm_num only
  have hm := summable_completed_poisson_terms hq hRH hp hne hinv hs
  have he := completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv hs
  rw [hr] at hm he
  norm_num only at hm he
  have ht := completed_gram_term_eq_poisson hRH hp hne hinv T
  refine ⟨(hm.mul_left 2).congr (fun ρ ↦ (ht ρ).symm), ?_⟩
  rw [tsum_congr ht, tsum_mul_left, he]
  ring

/-- Every finite actual Gram row is bounded by the full nonnegative completed-zero row.
Use summability and retain its exact conductor term. -/
theorem finite_completed_gram_row_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (S : Finset ℂ) (T : ℝ) :
    ∑ ρ ∈ S,
        (analyticOrderNatAt χ.completedLFunction ρ : ℝ) *
          PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (T - ρ.im) ≤
      Real.log q + 2 * (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + T * Complex.I)).re := by
  have h := completed_gram_row_sum hq hRH hp hne hinv T
  have hf :=
    Summable.sum_le_tsum S
      (fun ρ hρ ↦
        mul_nonneg (Nat.cast_nonneg _)
          (PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel_nonneg _))
      h.1
  rw [h.2] at hf
  exact hf

/-- Individual RH and an actual completed-derivative bound B at the finite zero heights
give energy at most (log q+2B) times the multiplicity-weighted coefficient l2 mass.
The conductor normalization is supplied internally by the Poisson identity. -/
theorem completed_zero_energy_le_rows {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (S : Finset ℂ) (a : ℂ → ℂ) {B : ℝ}
    (hB : ∀ ρ ∈ S, (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ B) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ)) ≤
      (Real.log q + 2 * B) *
        ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2 := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.energy_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ)) a (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  have hr := finite_completed_gram_row_le hq hRH hp hne hinv S ρ.im
  linarith only [hr, hB ρ hρ]

/-- For B nonnegative, the exact Dirichlet row bound controls every actual height prefix.
No assumed prefix energy or pair correlation is required. -/
theorem completed_zero_prefix_energy_le_rows {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (a : ℂ → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ ρ ∈ S, (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ B)
    (t : ℝ) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
            (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) t)) ≤
      (Real.log q + 2 * B) *
        ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2 := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.energy_prefix_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ)) a
      (add_nonneg (Real.log_natCast_nonneg q) (mul_nonneg (by norm_num only) hB0))
      (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  have hr := finite_completed_gram_row_le hq hRH hp hne hinv S ρ.im
  linarith only [hr, hB ρ hρ]

/-- Supply the exact completed Dirichlet row budget to the actual Abel block point theorem.
Both prefix and derivative energies are proved internally, with leading conductor term log q. -/
theorem completed_zero_block_point_le_rows {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (S : Finset ℂ) (a : ℂ → ℂ) {B U T : ℝ} (hB0 : 0 ≤ B) (hU : 0 ≤ U)
    (hUT : U ≤ T)
    (hB : ∀ ρ ∈ S, (logDeriv χ.completedLFunction (((5 / 2 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ B) :
    ‖PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) T)
              0 -
            PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt χ.completedLFunction ρ : ℝ) : ℂ) * a ρ) U)
              0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) *
        ((Real.log q + 2 * B) *
          ∑ ρ ∈ S, (analyticOrderNatAt χ.completedLFunction ρ : ℝ) * ‖a ρ‖ ^ 2) := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.block_point_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction ρ : ℝ)) a hU hUT
      (add_nonneg (Real.log_natCast_nonneg q) (mul_nonneg (by norm_num only) hB0))
      (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  have hr := finite_completed_gram_row_le hq hRH hp hne hinv S ρ.im
  linarith only [hr, hB ρ hρ]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
