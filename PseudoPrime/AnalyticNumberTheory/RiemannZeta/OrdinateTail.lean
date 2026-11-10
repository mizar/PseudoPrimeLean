/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZeroExclusion
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnconditionalZeroSumBounds

/-! # Inverse-square ordinate tails

A summable tail over all nontrivial zeros, preserving multiplicity and cutoff.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- At a nontrivial zero above height `T`, return its multiplicity divided
by its squared imaginary part; return zero elsewhere. The cutoff is strict. -/
noncomputable def ordinateTailWeight (T : ℝ) (ρ : ℂ) : ℝ :=
  if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2
  else 0

/-- The ordinate tail weight selects nontrivial zeros above the cutoff. -/
theorem ordinateTailWeight_eq (T : ℝ) (ρ : ℂ) :
    ordinateTailWeight T ρ =
      if riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im| then
        (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2
      else 0 := by
  rfl

/-- Under RH, each ordinate-tail weight is nonnegative and at most twice
the inverse-square xi-zero weight. The proved low-zero gap compares the
ordinate and norm denominators. -/
theorem ordinateTailWeight_bound (hRH : RiemannHypothesis) (T : ℝ) (ρ : ℂ) :
    0 ≤ ordinateTailWeight T ρ ∧
      ordinateTailWeight T ρ ≤ 2 * RiemannXi.inversePowerZeroWeight 2 ρ := by
  classical
  rw [ordinateTailWeight]
  split
  next h =>
    have hz := h.1
    have hre := h.2.1
    have hg := zero_height_gt_two_pi hRH hz hre
    have hg1 : 1 ≤ |ρ.im| := by nlinarith only [hg, Real.pi_gt_three]
    have hgpos : 0 < |ρ.im| := lt_of_lt_of_le (by norm_num only) hg1
    have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz hre
    have hr := RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hxi
    have hnorm : Complex.normSq ρ ≤ 2 * |ρ.im| ^ 2 := by
      rw [Complex.normSq_apply, hr, sq_abs]
      nlinarith only [hg1, abs_nonneg ρ.im, sq_abs ρ.im]
    have hn0 : 0 < Complex.normSq ρ := by
      have hn := zero_norm_ge20 hRH hz hre
      linarith only [hn]
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    · rw [← nontrivial_inverse_square_eq_weight hz hre]
      have hm : 0 ≤ (riemannZetaZeroMultiplicity ρ : ℝ) := Nat.cast_nonneg _
      have hh := mul_le_mul_of_nonneg_left hnorm hm
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ (sq_pos_of_pos hgpos) hn0).2
      nlinarith only [hh]
  next h =>
    constructor
    · exact le_rfl
    · exact mul_nonneg (by norm_num only) (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)

/-- Under RH, the inverse-square ordinate-tail weights are summable. Compare
them with twice the summable inverse-square xi-zero mass. -/
theorem ordinateTailWeight_summable (hRH : RiemannHypothesis) (T : ℝ) :
    Summable (ordinateTailWeight T) := by
  apply
    Summable.of_nonneg_of_le (fun ρ ↦ (ordinateTailWeight_bound hRH T ρ).1)
      (fun ρ ↦ (ordinateTailWeight_bound hRH T ρ).2)
  exact (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left 2

/-- The sum of multiplicity divided by squared absolute ordinate over all
nontrivial zeros strictly above `T`. It is summable under RH. -/
noncomputable def ordinateTail (T : ℝ) : ℝ :=
  ∑' ρ : ℂ, ordinateTailWeight T ρ

/-- The ordinate tail is the sum of its individual zero weights. -/
theorem ordinateTail_eq (T : ℝ) : ordinateTail T = ∑' ρ : ℂ, ordinateTailWeight T ρ := by rfl

/-- Under RH, the inverse-square ordinate sum over any finite set of
nontrivial zeros strictly above `T` is bounded by the full tail. Apply the
nonnegative summable-family finite-sum bound. -/
theorem finite_ordinate_tail_le (hRH : RiemannHypothesis) (S : Finset ℂ) (T : ℝ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (hT : ∀ ρ ∈ S, T < |ρ.im|) :
    (∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤ ordinateTail T := by
  have hs :=
    (ordinateTailWeight_summable hRH T).sum_le_tsum S
      (fun ρ _ ↦ (ordinateTailWeight_bound hRH T ρ).1)
  have he :
    (∑ ρ ∈ S, ordinateTailWeight T ρ) =
      ∑ ρ ∈ S, (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2 := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    simp only [ordinateTailWeight, hz ρ hρ, hre ρ hρ, hT ρ hρ, and_self, ↓reduceIte]
  rw [he] at hs
  exact hs

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
