/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.Analysis.LogarithmicCutoffBounds
public import PseudoPrime.Analysis.RefinedPart2Separation

/-! # The refined Part 2 character cutoff under GRH -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For q≥3000, GRH and nonprincipality exclude prime triviality below
(log(q)−2log(log(q))+5)². Apply the existing arbitrary-cutoff zero-defect core,
transfer the Riemann lower bounds, and use the refined polynomial separation.
This proves the analytic contradiction at the actual smaller cutoff. -/
theorem not_characterTrivialBelow_refinedRoot {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hL := (Analysis.eight_lt_log_level hq).le
  have ht8 := Analysis.eight_lt_logarithmicCutoffRoot hL
  have ht0 : 0 < Analysis.logarithmicCutoffRoot (Real.log q) :=
    lt_trans (by norm_num only : (0 : ℝ) < 8) ht8
  have hx := Analysis.sq_ge_64_of_ge_8 ht8.le
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt :
    Real.sqrt ((Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2) =
      Analysis.logarithmicCutoffRoot (Real.log q) :=
    Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log (Analysis.logarithmicCutoffRoot (Real.log q)) :=
    Real.log_nonneg (le_trans (by norm_num only) ht8.le)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
      (show 0 ≤ Analysis.logarithmicCutoffRoot (Real.log q) + 1 by linarith only [ht8])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    (Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2 -
        (1839 / 500 : ℝ) * Real.log (Analysis.logarithmicCutoffRoot (Real.log q)) -
        1 -
        (Analysis.logarithmicCutoffRoot (Real.log q) + 1) / 8 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2) χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass]
  exact
    Analysis.refinedPart2_bounds_incompatible ht8 hz (Analysis.le_logarithmicCutoffRoot_add_log hL)
      (log_conductor_div_pi_le χ) hR hb (by linarith only [hu]) hl

/-- Under GRH, a nonprincipal character of level q≥3000 has a prime with value
other than one below (log(q)−2log(log(q))+5)². Negate the no-witness condition
and apply the arbitrary-cutoff contradiction. Nonunit primes with value zero are allowed. -/
theorem exists_prime_not_one_le_refinedRoot {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  by_contra hh
  apply not_characterTrivialBelow_refinedRoot χ hne hq hGRH
  intro p hp hpx
  by_contra hv
  exact hh ⟨p, hp, hpx.le, hv⟩

/-- Under GRH, a nonprincipal character of level q≥3000 has a prime witness
below the minimum of (log(q))² and (log(q)−2log(log(q))+5)².
Choose the witness from the smaller of the old and refined cutoffs.
This is the strengthened Part 2 character theorem used by Miller–Rabin. -/
theorem exists_prime_not_one_le_refinedPart2Cutoff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log q) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2) ∧
        χ p ≠ 1 := by
  by_cases hs : (Real.log q) ^ 2 ≤ (Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2
  · obtain ⟨p, hp, hb, hv⟩ := exists_prime_not_one_le_log_sq χ hne hq hGRH
    exact
      ⟨p, hp, by
        rw [min_eq_left hs]; exact hb, hv⟩
  · obtain ⟨p, hp, hb, hv⟩ := exists_prime_not_one_le_refinedRoot χ hne hq hGRH
    exact
      ⟨p, hp, by
        rw [min_eq_right (le_of_not_ge hs)]; exact hb, hv⟩

/-- Under GRH, a proper subgroup of units at level q≥3000 has a prime outside
its image in ZMod(q), below the minimum of the old and refined Part 2 cutoffs.
Apply the refined character theorem to a nonprincipal quotient character.
Nonunit primes are outside the image and are permitted by this conclusion.
This is the subgroup interface used by the strengthened Miller–Rabin witness theorem. -/
theorem exists_prime_outside_subgroup_image_le_refinedPart2Cutoff {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log q) ^ 2) ((Analysis.logarithmicCutoffRoot (Real.log q)) ^ 2) ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_refinedPart2Cutoff (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
