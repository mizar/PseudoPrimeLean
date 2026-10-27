/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SharperTheorem11S2
public import PseudoPrime.Analysis.SmallStartPart2Bounds

/-! # Precise Part 2 at arbitrary coupled roots and smaller levels -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, a nonprincipal character cannot be trivial through t squared
when t exceeds eight and satisfies the precise coupled level inequality.
Apply the arbitrary-cutoff weighted comparison, retaining the conductor term.
This removes the fixed modulus entrance from the analytic core. -/
theorem not_characterTrivialBelow_of_precisePart2CoupledRoot {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {t : ℝ} (ht8 : 8 < t)
    (hlevel : (t - 2) * Real.log q ≤ (t - 2) * t + t * (2 * Real.log t - 2301 / 500)) :
    ¬LLSCharacterTrivialBelow χ (t ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 8) ht8
  have hx := Analysis.sq_ge_64_of_ge_8 ht8.le
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt : Real.sqrt (t ^ 2) = t := Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log t := Real.log_nonneg (le_trans (by norm_num only) ht8.le)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_233_div_10000
      (show 0 ≤ t + 1 by linarith only [ht8])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    t ^ 2 - (1839 / 500 : ℝ) * Real.log t - 1 - (42781 / 915500 : ℝ) * (t + 1) ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum (t ^ 2)
          χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass, ht0]
  have hP := Analysis.log_pi_ge_2096_div_1831
  exact
    Analysis.refinedPart2_bounds_incompatible_2301_div_500 ht8 hz hlevel
      (Analysis.log_le_third_of_ge_eight ht8.le) (log_conductor_div_pi_le_of_lower χ hP) hR hb
      (by linarith only [hu]) hl

/-- Under the arbitrary coupled-root assumptions, a nonprincipal character
has a prime non-one value through t squared. Negate prime triviality and
apply the generic analytic core. Character value zero remains allowed. -/
theorem exists_prime_not_one_of_precisePart2CoupledRoot {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {t : ℝ} (ht8 : 8 < t)
    (hlevel : (t - 2) * Real.log q ≤ (t - 2) * t + t * (2 * Real.log t - 2301 / 500)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ t ^ 2 ∧ χ p ≠ 1 := by
  by_contra hh
  apply not_characterTrivialBelow_of_precisePart2CoupledRoot χ hne hGRH ht8 hlevel
  intro p hp hpx
  by_contra hv
  exact hh ⟨p, hp, hpx.le, hv⟩

/-- Under GRH at q at least 1639, every nonprincipal character has a
prime non-one value through the precise Part 2 radius squared.
Use the logarithmic entrance 14803/2000 in the generic coupled-root theorem.
This is an analytic half-line result and uses no finite modulus table. -/
theorem exists_prime_not_one_le_sharperPart2Root_of_1639_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 1639 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  have hL := Analysis.log_level_ge_precisePart2_entrance hq
  exact
    exists_prime_not_one_of_precisePart2CoupledRoot χ hne hGRH
      (Analysis.eight_lt_sharperPart2Root_of_log_entrance hL)
      (Analysis.sharperPart2Root_coupled_of_log_entrance hL)

/-- Under GRH at q at least 1639, each proper unit subgroup misses a
prime through the precise Part 2 radius squared. Pull back a nonprincipal
character from the quotient. Nonunit primes are allowed in this image bound. -/
theorem exists_prime_outside_subgroup_image_le_sharperPart2Root_of_1639_le {q : ℕ} [NeZero q]
    (hq : 1639 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_sharperPart2Root_of_1639_le (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
