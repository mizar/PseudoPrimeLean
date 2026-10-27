/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S2
public import PseudoPrime.Analysis.SharperPart2CutoffBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.PreciseZeroMassBounds

/-! # Part 2 witnesses with additive correction 2301/500 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Any real lower bound c for log pi yields log(conductor/pi) ≤ log q-c
at a nonzero level. Use conductor divisibility and the real logarithm quotient
identity. This keeps the numerical log pi precision parameterized for later bounds. -/
theorem log_conductor_div_pi_le_of_lower {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {c : ℝ}
    (hc : c ≤ Real.log Real.pi) : Real.log ((χ.conductor : ℝ) / Real.pi) ≤ Real.log q - c := by
  have hf : 0 < (χ.conductor : ℝ) := Nat.cast_pos.mpr χ.conductor_ne_zero.bot_lt
  have hle : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  rw [Real.log_div hf.ne' Real.pi_ne_zero]
  exact sub_le_sub (Real.log_le_log hf hle) hc

/-- Under GRH, q ≥ 3000 and χ nonprincipal, prime triviality through
(log q-2 log log q+2301/500)² is impossible. Apply the arbitrary-cutoff core,
retain the coupled logarithmic level bound and use the rational polynomial separation.
The precise existing zero-mass and log pi constants improve the correction to 2301/500. -/
theorem not_characterTrivialBelow_sharperPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hL := (Analysis.eight_lt_log_level hq).le
  have ht8 := Analysis.eight_lt_sharperPart2CutoffRoot hL
  have ht0 : 0 < Analysis.sharperPart2CutoffRoot (Real.log q) :=
    lt_trans (by norm_num only : (0 : ℝ) < 8) ht8
  have hx := Analysis.sq_ge_64_of_ge_8 ht8.le
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt :
    Real.sqrt ((Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2) =
      Analysis.sharperPart2CutoffRoot (Real.log q) :=
    Real.sqrt_sq ht0.le
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hR hu
  have hz : 0 ≤ Real.log (Analysis.sharperPart2CutoffRoot (Real.log q)) :=
    Real.log_nonneg (le_trans (by norm_num only) ht8.le)
  have hT := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hz
  have hmass :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_233_div_10000
      (show 0 ≤ Analysis.sharperPart2CutoffRoot (Real.log q) + 1 by linarith only [ht8])
  rw [riemannLogLowerAt, hsqrt, Real.log_pow] at hS
  norm_num only [Nat.cast_ofNat] at hS
  have hl :
    (Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2 -
        (1839 / 500 : ℝ) * Real.log (Analysis.sharperPart2CutoffRoot (Real.log q)) -
        1 -
        (42781 / 915500 : ℝ) * (Analysis.sharperPart2CutoffRoot (Real.log q) + 1) ≤
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
          ((Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2) χ.primitiveCharacter).re := by
    nlinarith only [hS, hT, hmass, ht0]
  have hP := Analysis.log_pi_ge_2096_div_1831
  exact
    Analysis.refinedPart2_bounds_incompatible_2301_div_500 ht8 hz
      (Analysis.sharperPart2CutoffRoot_coupled_level_bound hL)
      (Analysis.log_le_third_of_ge_eight ht8.le) (log_conductor_div_pi_le_of_lower χ hP) hR hb
      (by linarith only [hu]) hl

/-- Under GRH at q ≥ 3000, each nonprincipal character has a prime p
with χ(p) ≠ 1 through (log q-2loglog q+2301/500)². Negate triviality and
apply the sharper comparison. Value zero is allowed, so coprimality is not claimed. -/
theorem exists_prime_not_one_le_sharperPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 3000 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  by_contra hh
  apply not_characterTrivialBelow_sharperPart2Root χ hne hq hGRH
  intro p hp hpx
  by_contra hv
  exact hh ⟨p, hp, hpx.le, hv⟩

/-- Under GRH at q ≥ 3000, a proper subgroup's image misses a prime
through the sharper Part 2 root squared. Pull back a nonprincipal quotient
character. Nonunits are allowed; this form feeds Miller-Rabin rejection. -/
theorem exists_prime_outside_subgroup_image_le_sharperPart2Root {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
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
    exists_prime_not_one_le_sharperPart2Root (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
