/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptiveReciprocalRadius
public import PseudoPrime.LLS.AnalyticFinerPart2FromFive
public import PseudoPrime.LLS.ReciprocalSavingPart1Root

/-! # Witness bounds retaining pointwise reciprocal losses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: GRH, a nonprincipal character and a modulus at least 600.
Claim: a non-one prime exists through the explicit adaptive squared radius.
Proof: use the pointwise reciprocal lower bound and the certified closed root condition.
Role: strictly improve the former finer radius on the entire admitted half-line. -/
theorem exists_prime_not_one_le_adaptivePart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 600 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  have hL := Analysis.log_level_ge_adaptivePart2_entrance hq
  have ht := Analysis.finerPart2Root_ge_thirty_six_fifths_of_639_div_100_le hL
  obtain ⟨hh, hx⟩ := Analysis.adaptivePart2Root_height_and_cutoff ht
  have ht7 : 7 ≤ Analysis.finerPart2CutoffRoot (Real.log q) := le_trans (by norm_num only) ht
  have hy : 0 < Analysis.adaptivePart2CutoffRoot (Real.log q) := by linarith only [hh]
  by_contra! hn
  apply
    not_characterTrivialBelow_of_sevenRoot χ hne hGRH hh hx
      (Analysis.pointwiseReciprocalLoss_ge_three_halves hh)
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_pointwise_loss hGRH.riemann
        hy (le_trans (by norm_num only) hx))
      (Analysis.coupled_level_bound_of_logarithmic_root_le (by linarith only [hL]) hy
        (by linarith only [Analysis.adaptivePart2Root_pointwise_condition ht7]))
  intro p hp hb
  exact hn p hp hb.le

/-- Input: GRH, a proper unit subgroup and a modulus at least 600.
Claim: an outside prime exists through the explicit adaptive squared radius.
Proof: pull back a nonprincipal quotient character and apply the character theorem.
Role: transfer the adaptive radius to primality-test witnesses; nonunits are allowed. -/
theorem exists_prime_outside_subgroup_le_adaptivePart2Root {q : ℕ} [NeZero q] (hq : 600 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_adaptivePart2Root (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- Input: GRH, nonprincipality, modulus at least 3000, and the exact-cost pointwise root condition.
Claim: a coprime non-one prime exists through the squared root.
Proof: use the variable reciprocal-saving criterion with the actual pointwise Riemann lower bound.
Role: retain both cutoff-dependent reciprocal loss and exact prime-power factor cost in Part 1. -/
theorem exists_prime_character_ne_one_of_pointwise_factor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (hB :
      2 * Real.log (Real.log q) + 7031 / 5000 +
            AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y -
          2 * reciprocalSavingAuxiliary q (Analysis.pointwiseReciprocalLoss y) ≤
        y - Real.log q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hx : (2 : ℝ) ≤ y ^ 2 := by nlinarith only [hL, hy]
  exact
    exists_prime_character_ne_one_of_reciprocal_saving_root χ hq hne hGRH hy
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_pointwise_loss hGRH.riemann
        hy0 hx)
      (div_nonneg (commonFactorLogWeightedSum_nonneg (sq_pos_of_pos hy0)) hy0.le) (le_refl _) hB

end PseudoPrime.LLS
