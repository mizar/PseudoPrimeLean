/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SevenPart2Bounds
public import PseudoPrime.LLS.SmallAnalyticFinerPart2

/-! # Entirely analytic finer Part 2 witnesses from level five -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: GRH, a nonprincipal character, root height seven and cutoff fifty,
and a reciprocal lower bound satisfying the coupled level condition.
Claim: prime triviality through the squared root is impossible.
Proof: construct the parameterized weighted core with log error -5/2 and separate its bounds.
Role: expose a reusable analytic interface for the lower cutoff regime. -/
theorem not_characterTrivialBelow_of_sevenRoot {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {t r : ℝ}
    (htRoot : (7 : ℝ) ≤ t) (hcutoff : 50 ≤ t ^ 2) (hrcost : (3 / 2 : ℝ) ≤ r)
    (hreciprocal :
      Real.log (t ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (t ^ 2))
    (hlevel : (t - 2) * Real.log q ≤ (t - 2) * t + t * (2 * Real.log t - (2 * r + 701 / 500))) :
    ¬LLSCharacterTrivialBelow χ (t ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 7) htRoot
  have hx := hcutoff
  have hcore :=
    weightedComparisonCore_of_trivialBelow_of_mainErrors χ hne hGRH
      (lt_of_lt_of_le (by norm_num only) hx)
      (Analysis.primitiveLogOddMainError_le_five_halves_of_ge_fifty hx)
      (Analysis.primitiveLogEvenMainError_le_five_halves_of_ge_fifty hx)
      (Analysis.primitiveReciprocalOddMainError_le_fixed_of_ge_twenty_six_half
        (le_trans (by norm_num only) hx))
      (Analysis.primitiveReciprocalEvenMainError_le_fixed_of_ge_twenty_six_half
        (le_trans (by norm_num only) hx))
      ht
  have hS :=
    re_characterLogWeightedSum_ge_of_defect_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann) χ.primitiveCharacter
      (lt_of_lt_of_le (by norm_num only) hx) hcore.logDefect_le
  have hR :=
    re_characterReciprocalWeightedSum_ge_of_pointwise_lower χ.primitiveCharacter hreciprocal
      hcore.reciprocalDefect_le
  have hb := hcore.zeroMass_le
  have hu := hcore.logWeighted_le
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log t := Real.log_nonneg (le_trans (by norm_num only) htRoot)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_233_div_10000
      (show 0 ≤ t + 1 by linarith only [htRoot])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    t ^ 2 - (1839 / 500 : ℝ) * Real.log t - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (t ^ 2)
          χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass, ht0]
  have hP := Analysis.log_pi_ge_2096_div_1831
  exact
    Analysis.refinedPart2_bounds_incompatible_of_root_ge_seven htRoot hz hrcost hlevel
      (Analysis.log_le_third_of_ge_six (by linarith only [htRoot]))
      (log_conductor_div_pi_le_of_lower χ hP) hR hb (by linarith only [hu]) hl

/-- Input: GRH, a nonprincipal character, and a level at least 501.
Claim: prime triviality through the finer squared radius is impossible.
Proof: instantiate the height-seven comparison with the precise reciprocal loss.
Role: close the high branch without finite modulus verification. -/
theorem not_characterTrivialBelow_finerPart2Root_from_501_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 501 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2) := by
  have hL := Analysis.log_level_ge_seven_root_entrance hq
  obtain ⟨hheight, hcutoff⟩ := Analysis.finerPart2Root_height_and_cutoff_of_ge_621_div_100 hL
  apply
    not_characterTrivialBelow_of_sevenRoot χ hne hGRH hheight hcutoff
      (by norm_num only : (3 / 2 : ℝ) ≤ 31551 / 20000)
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
        hGRH.riemann (le_trans (by norm_num only) hcutoff))
  have hc :=
    Analysis.logarithmicCutoffRoot_coupled_level_bound (c := (45571 / 10000 : ℝ))
      (by linarith only [hL])
      (show 0 < Analysis.finerPart2CutoffRoot (Real.log q) by linarith only [hheight])
      (show
        Analysis.finerPart2CutoffRoot (Real.log q) =
          Real.log q - 2 * Real.log (Real.log q) + 45571 / 10000
        from rfl)
  nlinarith only [hc]

/-- Input: GRH, a nonprincipal character, and a level at least five.
Claim: a prime through (log q-2 log log q+4.5571)^2 has value different from one.
Proof: use the reciprocal-only analytic branch through 500 and the height-seven branch above it.
Role: remove the finite modulus certificate premise from the improved character bound. -/
theorem exists_prime_not_one_le_finerPart2Root_from_five_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 5 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  by_contra! hn
  have ht : LLSCharacterTrivialBelow χ ((Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2) :=
    fun p hp hb ↦ hn p hp hb.le
  by_cases hsmall : q ≤ 500
  · exact not_characterTrivialBelow_finerPart2Root_small_analytic χ hne hq hsmall hGRH ht
  · exact
      not_characterTrivialBelow_finerPart2Root_from_501_analytic χ hne
        (Nat.succ_le_of_lt (Nat.lt_of_not_ge hsmall)) hGRH ht

/-- Input: GRH, a level at least five, and a proper unit subgroup.
Claim: a prime through the finer squared radius lies outside the subgroup image.
Proof: apply the analytic character theorem to a quotient character.
Role: give the proper-subgroup counterpart without small-prime exclusion or modulus enumeration. -/
theorem exists_prime_outside_finerPart2_from_five_analytic {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_finerPart2Root_from_five_analytic (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
