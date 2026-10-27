/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.SharperTheorem11S2
public import PseudoPrime.Analysis.Below64MainErrorBounds
public import PseudoPrime.Analysis.ReciprocalCostPart2Bounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ParameterizedReciprocalLowerBound
public import PseudoPrime.LLS.ParameterizedWeightedComparisonGRH

/-! # Part 2 with parameterized reciprocal loss -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Any pointwise lower bound for the Riemann reciprocal sum transfers
to a character sum after subtracting its defect upper bound.
Unfold the defect and compare the two inequalities. No fixed reciprocal loss
or cutoff hypothesis is needed by this algebraic interface. -/
theorem re_characterReciprocalWeightedSum_ge_of_pointwise_lower {f : ℕ} [NeZero f]
    (ψ : DirichletCharacter ℂ f) {X r d : ℝ}
    (hR : Real.log X - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum X)
    (hd : weightedReciprocalDefect ψ X ≤ d) :
    Real.log X - r - d ≤
      (AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum X ψ).re := by
  unfold weightedReciprocalDefect at hd
  linarith only [hR, hd]

/-- Under GRH, a nonprincipal character cannot be trivial through t squared
when t exceeds 15/2, its square is at least 59, and a reciprocal loss r
at least 3/2 satisfies the displayed pointwise lower and coupled level bounds.
Apply the arbitrary-cutoff weighted comparison, retaining the conductor term.
This retains the reciprocal loss as an input to the analytic core. -/
theorem not_characterTrivialBelow_of_reciprocalCostCoupledRoot {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {t r : ℝ}
    (htRoot : (15 / 2 : ℝ) < t) (hcutoff : 59 ≤ t ^ 2) (hrcost : (3 / 2 : ℝ) ≤ r)
    (hreciprocal :
      Real.log (t ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (t ^ 2))
    (hlevel : (t - 2) * Real.log q ≤ (t - 2) * t + t * (2 * Real.log t - (2 * r + 701 / 500))) :
    ¬LLSCharacterTrivialBelow χ (t ^ 2) := by
  intro ht
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have ht0 : 0 < t := lt_trans (by norm_num only : (0 : ℝ) < 15 / 2) htRoot
  have hx := hcutoff
  have hcore :=
    weightedComparisonCore_of_trivialBelow_of_mainErrors χ hne hGRH
      (lt_of_lt_of_le (by norm_num only) hx) (Analysis.primitiveLogOddMainError_le_fixed_of_ge59 hx)
      (Analysis.primitiveLogEvenMainError_le_fixed_of_ge59 hx)
      (Analysis.primitiveReciprocalOddMainError_le_fixed_of_ge59 hx)
      (Analysis.primitiveReciprocalEvenMainError_le_fixed_of_ge59 hx) ht
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
  have hz : 0 ≤ Real.log t := Real.log_nonneg (le_trans (by norm_num only) htRoot.le)
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
    Analysis.refinedPart2_bounds_incompatible_of_reciprocal_cost htRoot hz hrcost hlevel
      (Analysis.log_le_third_of_ge_six (by linarith only [htRoot]))
      (log_conductor_div_pi_le_of_lower χ hP) hR hb (by linarith only [hu]) hl

/-- Under the arbitrary coupled-root assumptions, a nonprincipal character
has a prime non-one value through t squared. Negate prime triviality and
apply the generic reciprocal-cost core. Character value zero remains allowed. -/
theorem exists_prime_not_one_of_reciprocalCostCoupledRoot {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {t r : ℝ}
    (htRoot : (15 / 2 : ℝ) < t) (hcutoff : 59 ≤ t ^ 2) (hrcost : (3 / 2 : ℝ) ≤ r)
    (hreciprocal :
      Real.log (t ^ 2) - r ≤ AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum (t ^ 2))
    (hlevel : (t - 2) * Real.log q ≤ (t - 2) * t + t * (2 * Real.log t - (2 * r + 701 / 500))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ t ^ 2 ∧ χ p ≠ 1 := by
  by_contra hh
  apply
    not_characterTrivialBelow_of_reciprocalCostCoupledRoot χ hne hGRH htRoot hcutoff hrcost
      hreciprocal hlevel
  intro p hp hpx
  by_contra hv
  exact hh ⟨p, hp, hpx.le, hv⟩

/-- Under GRH at q at least 1120, every nonprincipal character has a
prime non-one value through the precise Part 2 radius squared.
Use the logarithmic entrance 175527/25000 in the generic coupled-root theorem.
This is an analytic half-line result and uses no finite modulus table. -/
theorem exists_prime_not_one_le_reciprocalPart2Root {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hq : 1120 ≤ q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (Analysis.reciprocalPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  have hL := Analysis.log_level_ge_reciprocalPart2_entrance hq
  obtain ⟨hheight, hcutoff⟩ := Analysis.reciprocalPart2Root_height_and_cutoff hL
  apply
    exists_prime_not_one_of_reciprocalCostCoupledRoot χ hne hGRH hheight hcutoff
      (by norm_num only : (3 / 2 : ℝ) ≤ 789 / 500)
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_789_div_500
        hGRH.riemann (le_trans (by norm_num only) hcutoff))
  have hc :=
    Analysis.logarithmicCutoffRoot_coupled_level_bound (c := (2279 / 500 : ℝ))
      (by linarith only [hL]) (by linarith only [hheight])
      (show
        Analysis.reciprocalPart2CutoffRoot (Real.log q) =
          Real.log q - 2 * Real.log (Real.log q) + 2279 / 500
        from rfl)
  nlinarith only [hc]

/-- Under GRH at q at least 1120, each proper unit subgroup misses a
prime through the precise Part 2 radius squared. Pull back a nonprincipal
character from the quotient. Nonunit primes are allowed in this image bound. -/
theorem exists_prime_outside_subgroup_image_le_reciprocalPart2Root {q : ℕ} [NeZero q]
    (hq : 1120 ≤ q) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.reciprocalPart2CutoffRoot (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_reciprocalPart2Root (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

/-- Under GRH at levels at least 18000, each nonprincipal character
has a prime through the reciprocal-cost radius and strictly below log(q)^2.
Use the same witness and the strict half-line comparison of the radius.
The character value may still be zero. -/
theorem exists_prime_not_one_le_reciprocalPart2Root_and_lt_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 18000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.reciprocalPart2CutoffRoot (Real.log q)) ^ 2 ∧
        (p : ℝ) < (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_not_one_le_reciprocalPart2Root χ hne (le_trans (by norm_num only) hq) hGRH
  exact ⟨p, hp, hb, hb.trans_lt (Analysis.reciprocalPart2Root_sq_lt_log_sq_of_18000_le hq), hv⟩

end PseudoPrime.LLS
