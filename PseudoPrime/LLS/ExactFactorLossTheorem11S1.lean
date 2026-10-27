/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RetainedSavingTheorem11S1

/-! # Part 1 witnesses with the exact common-factor logarithmic cost -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a positive cutoff and any modulus.
Claim: the exact common-factor logarithmic cost is nonnegative.
Proof: every index in its finite support has nonnegative Mangoldt logarithmic weight.
Role: supply the nonnegative loss parameter to scalar separation. -/
theorem commonFactorLogWeightedSum_nonneg {q : ℕ} {x : ℝ} (hx : 0 < x) :
    0 ≤ AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x q := by
  apply Finset.sum_nonneg
  intro n hn
  have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
  exact AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg hx hi.1 hi.2

/-- Input: GRH, level at least 3000, a root above the level logarithm, and prime triviality.
Claim: the Riemann lower bound loses exactly the common-factor sum at the chosen cutoff.
Proof: retain the exact support identity and normalize its cost by the positive root.
Role: avoid replacing prime-power contributions by a distinct-prime count. -/
theorem characterLogWeightedSum_re_ge_exact_factor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1) :
    y ^ 2 -
        y *
          (2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass +
            AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y) -
        Real.log (2 * Real.pi) * Real.log (y ^ 2) -
        1 -
        2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (y ^ 2) χ).re := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hx : (1 : ℝ) < y ^ 2 := by nlinarith only [hL, hy]
  have hr := llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann (y ^ 2) hx
  rw [AnalyticNumberTheory.Arithmetic.characterLogWeightedSum_re_eq_sub_common_of_prime_trivial
      (y ^ 2) χ (zero_lt_one.trans hx) htrivial]
  rw [Real.sqrt_sq hy0.le] at hr
  have hc :=
    mul_div_cancel₀ (AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q) hy0.ne'
  nlinarith only [hr, hc]

/-- Input: GRH, a nonprincipal character, level at least 3000, and an admissible root.
The root increment dominates the retained-saving correction with the exact common-factor cost.
Claim: a coprime prime with non-one character value exists through the squared root.
Proof: combine the exact lower bound with the existing arbitrary-root upper bound and separation.
Role: expose a factorization-sensitive witness criterion without a new explicit formula. -/
theorem exists_prime_character_ne_one_of_exact_factor_root {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 3000 ≤ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (hB :
      2 * Real.log (Real.log q) + 7031 / 5000 +
            AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y -
          2 * refinedAuxiliaryTerm q ≤
        y - Real.log q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ y ^ 2 := by
  by_contra hn
  have htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ y ^ 2 → χ p = 1 := by
    intro p hp hd hb
    by_contra hv
    exact hn ⟨p, hp, hd, hv, hb⟩
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hprim : χ.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hN : 2 ≤ χ.conductor :=
    Nat.succ_le_iff.mpr
      (Nat.lt_of_le_of_ne (NeZero.pos χ.conductor)
        (Ne.symm
          (AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one
            hprim)))
  have hu := characterLogWeightedSum_re_le_refined_root χ hq hN hprim hGRH hy htrivial
  have hl := characterLogWeightedSum_re_ge_exact_factor_root χ hq hGRH hy htrivial
  have hP : (57 / 50 : ℝ) ≤ Real.log Real.pi := by
    have hp := Analysis.log_two_mul_pi_gt
    rw [Real.log_mul (by norm_num only) Real.pi_ne_zero] at hp
    linarith only [hp, Real.log_two_lt_d9]
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hw := div_nonneg (commonFactorLogWeightedSum_nonneg (q := q) (sq_pos_of_pos hy0)) hy0.le
  exact
    Analysis.refinedPart1_bounds_incompatible_retained_saving hL hy (le_max_left _ _) hw
      AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000 hP
      Analysis.log_two_mul_pi_lt.le hB hu hl

/-- Input: level at least 3000 and a root above its logarithm.
Claim: the exact normalized common-factor cost is at most the old distinct-prime cost.
Proof: combine the uniform common-factor bound with the decreasing squared-log ratio.
Role: show that the exact-cost root criterion is no stronger than the existing one. -/
theorem exact_factor_cost_le_distinct_prime_cost {q : ℕ} (hq : 3000 ≤ q) {y : ℝ}
    (hy : Real.log q ≤ y) :
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y ≤
      2 * q.primeFactors.card * (Real.log (Real.log q)) ^ 2 / Real.log q := by
  have hL := Analysis.eight_lt_log_level hq
  have hy0 : 0 < y := by linarith only [hL, hy]
  have hc :=
    AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum_le
      (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num only : (0 : ℕ) < 3000) hq)) (sq_pos_of_pos hy0)
  have hl := log_sq_root_le_level_ratio hq hy
  have hm :=
    mul_le_mul_of_nonneg_left hl
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) (Nat.cast_nonneg q.primeFactors.card))
  apply (div_le_iff₀ hy0).mpr
  simp only [div_eq_mul_inv] at hm ⊢
  nlinarith only [hc, hm]

/-- Input: GRH, a proper unit subgroup, and the exact-cost root criterion.
Claim: a coprime prime outside the subgroup image exists through the squared root.
Proof: apply the character criterion to a nonprincipal quotient character.
Role: provide the proper-subgroup form of the exact prime-power loss improvement. -/
theorem exists_prime_outside_subgroup_of_exact_factor_root {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : Real.log q ≤ y)
    (hB :
      2 * Real.log (Real.log q) + 7031 / 5000 +
            AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum (y ^ 2) q / y -
          2 * refinedAuxiliaryTerm q ≤
        y - Real.log q) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ (p : ℝ) ≤ y ^ 2 ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    exists_prime_character_ne_one_of_exact_factor_root (pullbackCharacter χ') hq
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hGRH hy hB
  refine ⟨p, hp, hd, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
