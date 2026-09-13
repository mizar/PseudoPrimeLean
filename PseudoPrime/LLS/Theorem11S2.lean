/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.WeightedComparisonGRH
import PseudoPrime.LLS.Theorem11S2Numerics
import PseudoPrime.LLS.Theorem11S1Subgroup
import PseudoPrime.LLS.RiemannLogResidueBound
import PseudoPrime.LLS.RiemannReciprocalResidueBound
import PseudoPrime.Analysis.LogarithmicConstants

/-! # Theorem 1.1 S2 from the common weighted comparison -/

namespace PseudoPrime.LLS

/-- The primitive conductor contributes at most `log q - 1` after division by `π`.
The conductor divides the level, and `log π ≥ 1`. This bound supplies the scalar
conductor input for S2 without imposing primitivity on the original character. -/
theorem log_conductor_div_pi_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Real.log ((χ.conductor : ℝ) / Real.pi) ≤ Real.log q - 1 := by
  have hc : 0 < (χ.conductor : ℝ) := by exact_mod_cast χ.conductor_ne_zero.bot_lt
  have hle : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  rw [Real.log_div hc.ne' Real.pi_ne_zero]
  exact sub_le_sub (Real.log_le_log hc hle) Analysis.zeroStar_log_pi_lower

/-- A nontrivial character cannot be trivial on every prime strictly below `(log q)^2`
when `q ≥ 3000`. Transfer to its primitive character and instantiate the zero-defect
common core; the reciprocal bound controls the zero mass and the logarithmic bounds
then have a strict numerical gap. This is the analytic contradiction used by S2. -/
theorem not_characterTrivialBelow_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 3000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬ LLSCharacterTrivialBelow χ ((Real.log q) ^ 2) := by
  intro ht
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hy := (Analysis.eight_lt_log_level hq).le
  have hx := Analysis.sq_ge_64_of_ge_8 hy
  have hcore := weightedComparisonCore_of_trivialBelow χ hne hGRH hx ht
  obtain ⟨hS, hR, hb, hu⟩ :=
    re_characterLogWeightedSum_ge_and_zeroMass_le_and_logWeighted_le
      (llsRiemannWeightedLowerBound_of_riemannHypothesis hGRH.riemann)
      (llsRiemannReciprocalLowerBound_of_riemannHypothesis hGRH.riemann)
      (lt_of_lt_of_le (by norm_num only) hx) (le_trans (by norm_num only) hx) hcore
  have hsqrt : Real.sqrt ((Real.log q) ^ 2) = Real.log q :=
    Real.sqrt_sq (le_trans (by norm_num only) hy)
  simp only [sub_zero] at hS hR
  rw [Real.log_pow] at hR
  rw [hsqrt] at hb
  rw [hsqrt, Real.log_pow] at hu
  norm_num only at hR hu
  have hF := log_conductor_div_pi_le χ
  have hb' := theorem11S2_zeroMass_le hy hF hR hb
  have hu' := theorem11S2_logWeighted_le
    (S := (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum
      ((Real.log q) ^ 2) χ.primitiveCharacter).re)
    hy (hF.trans (sub_le_self _ (by norm_num only))) hb'
    (by nlinarith only [hu])
  exact (not_le_of_gt (theorem11S2_upper_lt_riemann_lower hy)) (hS.trans hu')

/-- Under GRH, a nontrivial character has a prime with value different from `1`
below the S2 cutoff. The value may be zero, which is sufficient to exclude membership
in the image of a subgroup of units. -/
theorem exists_prime_not_one_le_log_sq {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 3000 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Real.log q) ^ 2 ∧ χ p ≠ 1 := by
  by_contra! h
  apply not_characterTrivialBelow_log_sq χ hne hq hGRH
  intro p hp hpx
  exact h p hp hpx.le

/-- GRH implies the paper's proper-subgroup S2 statement with its original cutoff
and hypotheses. Pull back a nontrivial quotient character; its prime witness cannot
be represented by a member of the subgroup. This preserves the nonunit endpoint
allowed by the public S2 specification. -/
theorem llsTheorem11S2_of_grh
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) : llsTheorem11S2 := by
  intro q _ hq _ H hH
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx
  obtain ⟨p, hp, hb, hn⟩ := exists_prime_not_one_le_log_sq (pullbackCharacter χ')
    (pullbackCharacter_ne_one_of_ne_one χ' hχ) hq hGRH
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, heq⟩
  apply hn
  rw [← heq]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS
