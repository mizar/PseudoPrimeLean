/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SubsquarePart2Separation
public import PseudoPrime.LLS.RationalTheorem11S2

/-! # A strictly smaller logarithmic square from an arbitrary-cutoff comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a natural level at least 3000.
Claim: subtracting 1/1000 from its logarithm leaves a cutoff root at least eight.
Proof: use explicit logarithm bounds at 3000 and monotonicity.
This places the entire analytic range within the arbitrary-cutoff core. -/
theorem eight_le_log_sub_mill_of_ge_3000 {q : ℕ} (hq : 3000 ≤ q) : 8 ≤ Real.log q - 1 / 1000 := by
  have hbase : (8001 / 1000 : ℝ) < Real.log 3000 := by
    rw [show (3000 : ℝ) = 3 * 2 ^ 3 * 5 ^ 3 by norm_num only,
      Real.log_mul (by norm_num only : (3 * 2 ^ 3 : ℝ) ≠ 0) (by norm_num only : (5 ^ 3 : ℝ) ≠ 0),
      Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0) (by norm_num only : (2 ^ 3 : ℝ) ≠ 0),
      Real.log_pow, Real.log_pow]
    norm_num only
    linarith only [Real.log_two_gt_d9, Real.log_three_gt_d9, Real.log_five_gt_d9]
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr hq)
  linarith only [hbase, hm]

/-- Input: GRH, level at least 3000 and a nonprincipal character.
Claim: not every prime strictly below the smaller squared root has character value one.
Proof: combine the arbitrary-cutoff core with the all-scale polynomial separation.
This eliminates a no-witness assumption without any finite input enumeration. -/
theorem not_characterTrivialBelow_strictLogSquare {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Real.log q - 1 / 1000) ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have ht8 := eight_le_log_sub_mill_of_ge_3000 hq
  have ht0 : 0 < Real.log q - 1 / 1000 := (by norm_num only : (0 : ℝ) < 8).trans_le ht8
  have hx := Analysis.sq_ge_64_of_ge_8 ht8
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt : Real.sqrt ((Real.log q - 1 / 1000) ^ 2) = Real.log q - 1 / 1000 :=
    Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log (Real.log q - 1 / 1000) :=
    Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 8).trans ht8)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
      (show 0 ≤ Real.log q - 1 / 1000 + 1 by linarith only [ht8])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    (Real.log q - 1 / 1000) ^ 2 - (1839 / 500 : ℝ) * Real.log (Real.log q - 1 / 1000) - 1 -
        (Real.log q - 1 / 1000 + 1) / 8 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum ((Real.log q - 1 / 1000) ^ 2)
          χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass]
  exact
    Analysis.subsquarePart2_bounds_incompatible ht8 (by linarith only [log_conductor_div_pi_le χ])
      hR hb (by linarith only [hu]) hl

/-- Input: GRH, level at least 3000 and a nonprincipal character.
Claim: a prime below the smaller squared root has value other than one.
Proof: negate prime triviality using the analytic contradiction.
Nonunit primes are permitted; this interface also applies to proper subgroup images. -/
theorem exists_prime_not_one_le_strictLogSquare {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Real.log q - 1 / 1000) ^ 2 ∧ χ p ≠ 1 := by
  by_contra h
  apply not_characterTrivialBelow_strictLogSquare χ hne hq hGRH
  intro p hp hpx
  by_contra hv
  exact h ⟨p, hp, hpx.le, hv⟩

/-- Input: GRH, level at least 3000 and a proper unit subgroup.
Claim: some prime through the smaller squared root lies outside its image.
Proof: pull back a nonprincipal character from the quotient group.
This supplies the subgroup estimate used by the MR witness theorem. -/
theorem exists_prime_outside_subgroup_image_le_strictLogSquare {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (Real.log q - 1 / 1000) ^ 2 ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_strictLogSquare (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
