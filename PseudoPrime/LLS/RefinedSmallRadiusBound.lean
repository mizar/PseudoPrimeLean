/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.ResidueSubgroup
public import PseudoPrime.LLS.PaperStatements.GammaUniformSmallScaleBounds
public import PseudoPrime.LLS.GammaUniformRationalProfileBounds
public import PseudoPrime.LLS.PaperStatements.GammaUniformRationalProfileBounds
public import PseudoPrime.LLS.RefinedTheorem11S1Subgroup

/-! # Rational coefficient-0.796 witnesses from modulus 3000 -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For 3000 ≤ q < 20000, the refined Part 1 radius root is at most seventy.
Bound log q by ten, its logarithm by three, and the distinct prime count by twenty-two.
Discard the nonnegative reciprocal saving to bound the correction by sixty.
This transfers the small modulus range without new exhaustive certificates. -/
theorem refinedRadiusRoot_le_seventy_of_lt_20000 {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (hsmall : q < 20000) : refinedRadiusRoot q ≤ 70 := by
  let L := Real.log q
  let z := Real.log L
  have hL := Analysis.eight_lt_log_level hq
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hlog20 := Real.log_le_log hqpos (by exact_mod_cast hsmall.le : (q : ℝ) ≤ 20000)
  rw [show (20000 : ℝ) = 2 * (2 * 5) ^ 4 by norm_num only,
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0)
      (pow_ne_zero 4 (by norm_num only : (2 * 5 : ℝ) ≠ 0)),
    Real.log_pow,
    Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (by norm_num only : (5 : ℝ) ≠ 0)] at hlog20
  norm_num only [Nat.cast_ofNat] at hlog20
  have hLupper : L ≤ 10 := by linarith only [hlog20, Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hL0 : 0 < L := by linarith only [hL]
  have hz0 : 0 ≤ z := Real.log_nonneg (show 1 ≤ L by linarith only [hL])
  have hz := Real.log_le_sub_one_of_pos (div_pos hL0 (by norm_num only : (0 : ℝ) < 4))
  rw [Real.log_div hL0.ne' (by norm_num only : (4 : ℝ) ≠ 0), show (4 : ℝ) = 2 ^ 2 by norm_num only,
    Real.log_pow] at hz
  norm_num only [Nat.cast_ofNat] at hz
  have hzupper : z ≤ 3 := by
    dsimp only [z]
    linarith only [hz, hLupper, Real.log_two_lt_d9]
  have hcard :=
    AnalyticNumberTheory.Arithmetic.primeFactors_card_le_cutoff_add_log_div (NeZero.ne q)
      (by norm_num only : (1 : ℝ) < 2)
  have hdiv : L / Real.log 2 ≤ 2 * L := by
    apply (div_le_iff₀ (show (0 : ℝ) < Real.log 2 by linarith only [Real.log_two_gt_d9])).mpr
    have h := mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le hL0.le
    nlinarith only [h, hL0]
  have hcard22 : (q.primeFactors.card : ℝ) ≤ 22 := by linarith only [hcard, hdiv, hLupper]
  have hzsq : z ^ 2 ≤ 9 := by nlinarith only [hz0, hzupper]
  have hnum := mul_le_mul_of_nonneg_right hcard22 (sq_nonneg z)
  have hw : 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L ≤ 50 := by
    rw [div_le_iff₀ hL0]
    nlinarith only [hnum, hzsq, hL]
  have hA : 0 ≤ refinedAuxiliaryTerm q := le_max_left _ _
  have hB : refinedCorrectionTerm q ≤ 60 := by
    unfold refinedCorrectionTerm
    apply max_le (by norm_num only)
    change 2 * z + 2 + 2 * (q.primeFactors.card : ℝ) * z ^ 2 / L - 2 * refinedAuxiliaryTerm q ≤ 60
    linarith only [hzupper, hw, hA]
  dsimp only [refinedRadiusRoot]
  linarith only [hLupper, hB]

end PseudoPrime.LLS
