/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FinerPart2CutoffBounds
public import PseudoPrime.LLS.ReciprocalCostPart2Bounds
public import PseudoPrime.LLS.AnalyticFinerPart2FromFive
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # LLS Part 2 with correction 4.5571 from modulus five -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: GRH, a nonprincipal character and q>=1122.
Claim: a prime non-one value lies below the finer squared radius; zero values remain allowed.
Proof: use reciprocal loss 31551/20000 in the existing parameterized comparison.
Role: provide the analytic half-line behind the full subgroup-image theorem. -/
theorem exists_prime_not_one_le_finerPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 1122 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  have hL := Analysis.log_level_ge_finerPart2_entrance hq
  obtain ⟨hh, hcut⟩ := Analysis.finerPart2Root_height_and_cutoff hL
  apply
    exists_prime_not_one_of_reciprocalCostCoupledRoot χ hne hGRH hh hcut
      (by norm_num only : (3 / 2 : ℝ) ≤ 31551 / 20000)
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
        hGRH.riemann (le_trans (by norm_num only) hcut))
  have hc :=
    Analysis.logarithmicCutoffRoot_coupled_level_bound (c := (45571 / 10000 : ℝ))
      (by linarith only [hL]) (by linarith only [hh])
      (show
        Analysis.finerPart2CutoffRoot (Real.log q) =
          Real.log q - 2 * Real.log (Real.log q) + 45571 / 10000
        from rfl)
  nlinarith only [hc]

/-- Input: GRH, q>=1122 and a proper subgroup of the unit group.
Claim: a prime outside its image lies within the finer squared radius.
Proof: pull back a nonprincipal quotient character. Nonunit primes are allowed.
Role: supply the analytic branch of the entrance-five theorem. -/
theorem exists_prime_outside_finerPart2_analytic {q : ℕ} [NeZero q] (hq : 1122 ≤ q)
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
    exists_prime_not_one_le_finerPart2Root (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- Input: GRH, q>=5 and a proper subgroup of the unit group.
Claim: a prime outside its image lies below (log(q)-2*log(log(q))+4.5571)^2.
Proof: apply the entirely analytic entrance-five theorem, using a single radius throughout.
Role: improve the Part 2 constant while retaining entrance five. -/
theorem exists_prime_outside_finerPart2_from_five
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  exact exists_prime_outside_finerPart2_from_five_analytic hq H hH hGRH

end PseudoPrime.LLS
