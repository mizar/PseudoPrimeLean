/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalSavingPart1Root

/-! # Part 1 with reciprocal saving constant 31551/20000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a modulus. Output: the auxiliary saving with reciprocal loss 31551/20000.
Role: transfer the finer Riemann reciprocal lower bound to Part 1. -/
noncomputable def preciseSavingAuxiliary (q : ℕ) : ℝ :=
  reciprocalSavingAuxiliary q (31551 / 20000)

/-- Input: a modulus. Output: the retained-saving correction using the stronger auxiliary term.
Role: retain the original factor-count cost while strengthening the reciprocal saving. -/
noncomputable def preciseSavingCorrectionTerm (q : ℕ) : ℝ :=
  max 0
    (2 * Real.log (Real.log q) + 7031 / 5000 +
        2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
      2 * preciseSavingAuxiliary q)

/-- Input: a modulus. Output: log(q) plus the new nonnegative correction.
Role: define the explicit prime cutoff shared by analytic and finite proofs. -/
noncomputable def preciseSavingRadiusRoot (q : ℕ) : ℝ :=
  Real.log q + preciseSavingCorrectionTerm q

/-- Input: any modulus. Claim: the old auxiliary saving is at most the new one.
Proof: compare the reciprocal constants inside the maximum.
Role: verify the direction of the improvement independently of witness existence. -/
theorem refinedAuxiliaryTerm_le_preciseSavingAuxiliary (q : ℕ) :
    refinedAuxiliaryTerm q ≤ preciseSavingAuxiliary q := by
  dsimp only [refinedAuxiliaryTerm, preciseSavingAuxiliary, reciprocalSavingAuxiliary]
  apply max_le_max (le_refl _)
  linarith only

/-- Input: any modulus. Claim: the new radius root never exceeds the previous root.
Proof: the stronger auxiliary saving decreases the nonnegative correction.
Role: make the pointwise improvement explicit. -/
theorem preciseSavingRadiusRoot_le_retainedSavingRadiusRoot (q : ℕ) :
    preciseSavingRadiusRoot q ≤ retainedSavingRadiusRoot q := by
  have hA := refinedAuxiliaryTerm_le_preciseSavingAuxiliary q
  dsimp only [preciseSavingRadiusRoot, retainedSavingRadiusRoot, preciseSavingCorrectionTerm,
    retainedSavingCorrectionTerm]
  apply add_le_add_right
  apply max_le_max (le_refl _)
  linarith only [hA]

/-- Input: GRH, a nonprincipal character, and a modulus at least 3000.
Claim: a coprime non-one prime exists through the precise-saving squared radius.
Proof: instantiate the variable-loss root theorem with the finer Riemann lower bound.
Role: expose the explicit analytic improvement of Part 1. -/
theorem exists_prime_character_ne_one_le_preciseSavingRadius {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  have hy : Real.log q ≤ preciseSavingRadiusRoot q := le_add_of_nonneg_right (le_max_left _ _)
  have hL := Analysis.eight_lt_log_level hq
  have hx : (2 : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by nlinarith only [hL, hy]
  apply
    exists_prime_character_ne_one_of_reciprocal_saving_root χ hq hne hGRH hy
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
        hGRH.riemann hx)
      (div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (sq_nonneg _))
        (by linarith only [hL]))
      (exact_factor_cost_le_distinct_prime_cost hq hy)
  change _ ≤ Real.log q + preciseSavingCorrectionTerm q - Real.log q
  rw [add_sub_cancel_left]
  exact le_max_right _ _

/-- Input: GRH, nonprincipality, and the exact-factor root condition using the finer saving.
Claim: a coprime non-one prime exists through the squared root.
Proof: retain the exact common-factor cost in the variable-loss root criterion.
Role: combine both Part 1 improvements without weakening either cost. -/
theorem exists_prime_character_ne_one_of_precise_exact_factor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (hB :
      2 * Real.log (Real.log q) + 7031 / 5000 +
            AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y -
          2 * preciseSavingAuxiliary q ≤
        y - Real.log q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hx : (2 : ℝ) ≤ y ^ 2 := by nlinarith only [hL, hy]
  exact
    exists_prime_character_ne_one_of_reciprocal_saving_root χ hq hne hGRH hy
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
        hGRH.riemann hx)
      (div_nonneg (commonFactorLogWeightedSum_nonneg (sq_pos_of_pos hy0)) hy0.le) (le_refl _) hB

/-- Input: GRH, a proper unit subgroup, and a modulus at least 3000.
Claim: a coprime prime outside the subgroup image lies within the new squared radius.
Proof: use a nonprincipal character of the quotient.
Role: give the subgroup counterpart for the entrance-three extension. -/
theorem exists_prime_outside_subgroup_le_preciseSavingRadius {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬p ∣ q ∧
        (p : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    exists_prime_character_ne_one_le_preciseSavingRadius (pullbackCharacter χ') hq
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hGRH
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- Input: any modulus.
Claim: the auxiliary saving increases by at most the reciprocal-loss difference.
Proof: compare both branches of its maximum with zero.
Role: quantify the change without assuming either branch is active. -/
theorem preciseSavingAuxiliary_le_refined_add_loss_difference (q : ℕ) :
    preciseSavingAuxiliary q ≤ refinedAuxiliaryTerm q + ((32873 / 20800 : ℝ) - 31551 / 20000) := by
  have hz : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hr :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) - 32873 / 20800 -
        AnalyticNumberTheory.Arithmetic.primeFactorLogSum q)
  change _ ≤ refinedAuxiliaryTerm q at hr
  dsimp only [preciseSavingAuxiliary, reciprocalSavingAuxiliary]
  apply max_le
  · linarith only [hz]
  · linarith only [hr]

/-- Input: any modulus.
Claim: the radius root decreases by at most twice the reciprocal-loss difference.
Proof: transfer the auxiliary comparison through the nonnegative correction.
Role: bound the pointwise numerical improvement, including changes of maximum branches. -/
theorem retainedSavingRadiusRoot_sub_precise_le_loss_difference (q : ℕ) :
    retainedSavingRadiusRoot q - preciseSavingRadiusRoot q ≤
      2 * ((32873 / 20800 : ℝ) - 31551 / 20000) := by
  have hA := preciseSavingAuxiliary_le_refined_add_loss_difference q
  have hz : 0 ≤ preciseSavingCorrectionTerm q := le_max_left _ _
  have hr :=
    le_max_right (0 : ℝ)
      (2 * Real.log (Real.log q) + 7031 / 5000 +
          2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q -
        2 * preciseSavingAuxiliary q)
  change _ ≤ preciseSavingCorrectionTerm q at hr
  have hc :
    retainedSavingCorrectionTerm q ≤
      preciseSavingCorrectionTerm q + 2 * ((32873 / 20800 : ℝ) - 31551 / 20000) := by
    apply max_le
    · linarith only [hz]
    · linarith only [hr, hA]
  dsimp only [retainedSavingRadiusRoot, preciseSavingRadiusRoot]
  linarith only [hc]

end PseudoPrime.LLS
