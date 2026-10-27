/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SmallStartFinerPart2Bounds
public import PseudoPrime.Analysis.SmallReciprocalMainErrorBounds
public import PseudoPrime.LLS.ReciprocalCostPart2Bounds
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Reciprocal-only analytic Part 2 witnesses on the low modulus range -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: GRH, a nonprincipal character, and a level between five and five hundred.
Claim: prime triviality through the finer Part 2 squared radius is impossible.
Proof: use only the reciprocal explicit formula, its low-cutoff parity errors,
and the monotone negative scalar gap. No finite modulus enumeration is used.
Role: provide the low branch for an entirely analytic entrance from five. -/
theorem not_characterTrivialBelow_finerPart2Root_small_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 5 ≤ q) (hQ : q ≤ 500)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ¬LLSCharacterTrivialBelow χ ((Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2) := by
  intro ht
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor :=
    Nat.succ_le_iff.mpr
      (Nat.lt_of_le_of_ne (NeZero.pos χ.conductor)
        (Ne.symm
          (AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hnp)))
  have hL : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num only : (1 : ℕ) < 5) hq))
  have htlow := Analysis.finerPart2Root_ge_51571_div_10000 hL
  have htpos : 0 < Analysis.finerPart2CutoffRoot (Real.log q) := by linarith only [htlow]
  have hx := Analysis.finerPart2Root_sq_ge_twenty_six_half hL
  have hx1 : (1 : ℝ) < (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 := by linarith only [hx]
  have hraw :=
    primitiveReciprocalRaw_of_mainErrors hf hGRH hp hnp (inv_ne_one.mpr hnp) hx1
      (Analysis.primitiveReciprocalOddMainError_le_fixed_of_ge_twenty_six_half hx)
      (Analysis.primitiveReciprocalEvenMainError_le_fixed_of_ge_twenty_six_half hx)
  have hd :=
    weightedReciprocalDefect_eq_zero_of_trivialBelow (zero_lt_one.trans hx1)
      (characterTrivialBelow_primitiveCharacter ht)
  have hr :=
    re_characterReciprocalWeightedSum_ge_of_pointwise_lower χ.primitiveCharacter
      (AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
        hGRH.riemann (by linarith only [hx]))
      hd.le
  simp only [sub_zero] at hr
  rw [Real.log_pow] at hr
  norm_num only [Nat.cast_ofNat] at hr
  have hF := log_conductor_div_pi_le_of_lower χ Analysis.log_pi_ge_2096_div_1831
  rw [Real.log_div (by exact_mod_cast χ.conductor_ne_zero) Real.pi_ne_zero] at hF
  have hi : 0 ≤ 1 - 1 / (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 := by
    have hh :=
      div_le_one_of_le₀
        (show (1 : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 by linarith only [hx])
        (sq_nonneg _)
    linarith only [hh]
  have hprod := mul_le_mul_of_nonneg_left hF (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2) hi)
  have hL4 :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 4)
      (show (4 : ℝ) ≤ q by exact_mod_cast (le_trans (by norm_num only : (4 : ℕ) ≤ 5) hq))
  rw [Real.log_four_eq] at hL4
  have hLP : 0 ≤ Real.log (q : ℝ) - 2096 / 1831 := by linarith only [hL4, Real.log_two_gt_d9]
  have hloss :=
    mul_nonneg
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1)
        (sq_nonneg (Analysis.finerPart2CutoffRoot (Real.log q))))
      hLP
  have hb :=
    mul_nonneg (sq_nonneg (1 - 1 / Real.sqrt ((Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2)))
      (abs_nonneg (AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter))
  have hneg :=
    Analysis.finerPart2ReciprocalOnlyGap_neg_of_le_five_hundred hL
      (Real.log_le_log (by exact_mod_cast NeZero.pos q) (Nat.cast_le.mpr hQ))
  dsimp only [Analysis.finerPart2ReciprocalOnlyGap] at hneg
  nlinarith only [hr, hraw, hprod, hloss, hb, hneg]

/-- Input: GRH, a nonprincipal character, and a level between five and five hundred.
Claim: a prime through the finer squared radius has value different from one.
Proof: negate prime triviality and use the reciprocal-only analytic contradiction.
Role: expose the low analytic branch as a witness theorem. -/
theorem exists_prime_not_one_le_finerPart2Root_small_analytic {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 5 ≤ q) (hQ : q ≤ 500)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log q)) ^ 2 ∧ χ p ≠ 1 := by
  by_contra! hn
  apply not_characterTrivialBelow_finerPart2Root_small_analytic χ hne hq hQ hGRH
  intro p hp hb
  exact hn p hp hb.le

end PseudoPrime.LLS
