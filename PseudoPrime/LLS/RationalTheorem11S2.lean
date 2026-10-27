/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedTheorem11S2
public import PseudoPrime.Analysis.RationalPart2CutoffBounds

/-! # Rational Part 2 character and subgroup cutoff -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 3000 and χ nonprincipal, prime triviality through
(log q-2 log log q+193/40)² is impossible. Apply the arbitrary-cutoff core,
retain the coupled logarithmic level bound and use the rational polynomial separation.
This improves the additive Part 2 correction from five to 193/40. -/
theorem not_characterTrivialBelow_rationalPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hL := (Analysis.eight_lt_log_level hq).le
  have ht8 := Analysis.eight_lt_rationalPart2CutoffRoot hL
  have ht0 : 0 < Analysis.rationalPart2CutoffRoot (Real.log q) :=
    lt_trans (by norm_num only : (0 : ℝ) < 8) ht8
  have hx := Analysis.sq_ge_64_of_ge_8 ht8.le
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt :
    Real.sqrt ((Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2) =
      Analysis.rationalPart2CutoffRoot (Real.log q) :=
    Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log (Analysis.rationalPart2CutoffRoot (Real.log q)) :=
    Real.log_nonneg (le_trans (by norm_num only) ht8.le)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_sixteenth
      (show 0 ≤ Analysis.rationalPart2CutoffRoot (Real.log q) + 1 by linarith only [ht8])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    (Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2 -
        (1839 / 500 : ℝ) * Real.log (Analysis.rationalPart2CutoffRoot (Real.log q)) -
        1 -
        (Analysis.rationalPart2CutoffRoot (Real.log q) + 1) / 8 ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2) χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass]
  exact
    Analysis.refinedPart2_bounds_incompatible_193_div_40 ht8 hz
      (Analysis.rationalPart2CutoffRoot_coupled_level_bound hL)
      (Analysis.log_le_third_of_ge_eight ht8.le) (log_conductor_div_pi_le χ) hR hb
      (by linarith only [hu]) hl

/-- Under GRH, a nonprincipal character at q ≥ 3000 has a prime with
non-one value through (log q-2 log log q+193/40)². Negate prime triviality
and use the rational-cutoff contradiction. Nonunit primes are permitted. -/
theorem exists_prime_not_one_le_rationalPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  by_contra hh
  apply not_characterTrivialBelow_rationalPart2Root χ hne hq hGRH
  intro p hp hpx
  by_contra hv
  exact hh ⟨p, hp, hpx.le, hv⟩

/-- Under GRH, q ≥ 3000 and χ nonprincipal, a prime with non-one value
lies through the smaller of (log q)² and the rational Part 2 squared root.
Choose the witness at the smaller cutoff. This preserves pointwise priority. -/
theorem exists_prime_not_one_le_rationalPart2Cutoff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log q) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2) ∧
        χ p ≠ 1 := by
  by_cases hs : (Real.log q) ^ 2 ≤ (Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2
  · obtain ⟨p, hp, hb, hv⟩ := exists_prime_not_one_le_log_sq χ hne hq hGRH
    exact
      ⟨p, hp, by
        rw [min_eq_left hs]; exact hb, hv⟩
  · obtain ⟨p, hp, hb, hv⟩ := exists_prime_not_one_le_rationalPart2Root χ hne hq hGRH
    exact
      ⟨p, hp, by
        rw [min_eq_right (le_of_not_ge hs)]; exact hb, hv⟩

/-- Under GRH, q ≥ 3000 and H proper, a prime outside the subgroup image
lies through the minimum of the pure and rational Part 2 cutoffs.
Pull back a nonprincipal quotient character and apply its witness theorem.
Nonunit primes are allowed, as required by the Miller–Rabin transfer. -/
theorem exists_prime_outside_subgroup_image_le_rationalPart2Cutoff {q : ℕ} [NeZero q]
    (hq : 3000 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ min ((Real.log q) ^ 2) ((Analysis.rationalPart2CutoffRoot (Real.log q)) ^ 2) ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_rationalPart2Cutoff (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
