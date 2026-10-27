/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianSubgroupComparison
public import PseudoPrime.LLS.GammaLeftMomentBounds
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Explicit scale and error budgets for Gaussian Miller--Rabin witnesses

The scale (32/105)L² has certified square-root and fourth-root bounds.
At L≥225000000, the precise Gaussian secondary allowance is at most 2000,
and the complete normalized error is at most L/800.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The Gaussian MR scale (32/105)L². Multiplying by cutoff 21/10 gives
(16/25)L², the coefficient 0.64 target. -/
noncomputable def gaussianMRScale (L : ℝ) : ℝ :=
  (32 / 105 : ℝ) * L ^ 2

/-- The MR scale is nonnegative at every real logarithmic parameter.
The rational factor is positive and the remaining factor is a square. -/
theorem gaussianMRScale_nonneg (L : ℝ) : 0 ≤ gaussianMRScale L :=
  mul_nonneg (by norm_num only : (0 : ℝ) ≤ 32 / 105) (sq_nonneg L)

/-- For L≥0 the scale square root is at least (69/125)L.
Compare squares with the exact rational scale coefficient. -/
theorem gaussianMRScale_sqrt_lower {L : ℝ} (hL : 0 ≤ L) :
    (69 / 125 : ℝ) * L ≤ Real.sqrt (gaussianMRScale L) := by
  apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL) (gaussianMRScale_nonneg L)).mpr
  dsimp only [gaussianMRScale]
  nlinarith only [sq_nonneg L]

/-- For L≥0 the scale square root is at most (9/16)L.
Compare squares; this supplies the fourth-root upper bound. -/
theorem gaussianMRScale_sqrt_upper {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (gaussianMRScale L) ≤ (9 / 16 : ℝ) * L := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) hL
  · dsimp only [gaussianMRScale]
    nlinarith only [sq_nonneg L]

/-- For L≥0 the scale fourth root is at most (3/4)sqrt(L).
Identify the fourth root with the iterated square root and apply monotonicity. -/
theorem gaussianMRScale_fourth_root_le {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRScale L ^ (1 / 4 : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt L := by
  have he : gaussianMRScale L ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt (gaussianMRScale L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (gaussianMRScale_nonneg L)]
    norm_num only
  rw [he]
  have h := Real.sqrt_le_sqrt (gaussianMRScale_sqrt_upper hL)
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 9 / 16)] at h
  norm_num only [Real.sqrt_div] at h
  exact h

/-- For L≥225000000, the MR scale exceeds 3¹⁶.
Compare squares to supply the existing left-moment decay range. -/
theorem gaussianMRScale_ge_three_pow_sixteen {L : ℝ} (hL : 225000000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ gaussianMRScale L := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 225000000) hL 2
  dsimp only [gaussianMRScale]
  nlinarith only [hs]

/-- At L≥225000000 and log q≤L, the precise Gaussian ambient error
is at most 2000. Bound its pole and left-moment terms by three each,
retaining the fixed zero and archimedean costs. -/
theorem gaussianMR_ambient_error_le {q : ℕ} {L : ℝ} (hL : 225000000 ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMRScale L) ≤ 2000 := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 225000000).trans_le hL
  have hs := gaussianMRScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (gaussianMRScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 69 / 125) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (gaussianMRScale L)) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (gaussianMRScale_ge_three_pow_sixteen hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) / (3 * Real.sqrt (gaussianMRScale L)) ≤
      3 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, hq, hs]
  have hJ :
    (11 / 10 : ℝ) * gaussianMRScale L ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      3 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]

/-- At L≥225000000, sqrt(L)≤L/15000.
The square-root threshold 15000 and its exact square supply the error absorption. -/
theorem gaussianMR_sqrt_log_absorption {L : ℝ} (hL : 225000000 ≤ L) : Real.sqrt L ≤ L / 15000 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 225000000).trans hL
  have hs : (15000 : ℝ) ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num only) hL0).mpr
      (by
        norm_num only; exact hL)
  have hprod := mul_nonneg (Real.sqrt_nonneg L) (sub_nonneg.mpr hs)
  nlinarith only [hprod, Real.sq_sqrt hL0]

/-- At L≥225000000 and log q≤L, principal and secondary Gaussian errors
total at most L/800 after index normalization. Combine the fourth-root estimate
with the certified ambient error 2000 and the square-root absorption. -/
theorem gaussianMR_error_budget {q : ℕ} {L : ℝ} (hL : 225000000 ≤ L) (hq : Real.log q ≤ L) :
    (70 / 3 : ℝ) * gaussianMRScale L ^ (1 / 4 : ℝ) +
        LLS.PaperStatements.gaussianAmbientError q (gaussianMRScale L) ≤
      L / 800 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 225000000).trans hL
  have hfour := gaussianMRScale_fourth_root_le hL0
  have hs := gaussianMR_sqrt_log_absorption hL
  have he := gaussianMR_ambient_error_le hL hq
  nlinarith only [hfour, hs, he, hL]

/-- For positive L and error at most L/800, the normalized Gaussian main
term exceeds (161/400)L plus the error. The rational root bound leaves a strict
positive margin at coefficient 16/25 and cutoff 21/10. -/
theorem gaussianMR_main_term_lt {L E : ℝ} (hL : 0 < L) (hE : E ≤ L / 800) :
    (161 / 400 : ℝ) * L + E < (21943 / 30000 : ℝ) * Real.sqrt (gaussianMRScale L) := by
  have hs := gaussianMRScale_sqrt_lower hL.le
  nlinarith only [hs, hE, hL]

/-- A decimal cutoff 10^d≤n gives log n≥(23/10)d.
Use logarithmic monotonicity and the proved lower bound for log 10.
Keep d variable to avoid evaluating enormous natural powers. -/
theorem gaussianMR_log_of_decimal {n d : ℕ} (hn : 10 ^ d ≤ n) : (23 / 10 : ℝ) * d ≤ Real.log n := by
  have h :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) d)
      (by exact_mod_cast hn : (10 : ℝ) ^ d ≤ n)
  rw [Real.log_pow] at h
  exact
    (mul_le_mul_of_nonneg_right log_ten_gt_twenty_three_tenths.le (Nat.cast_nonneg d)).trans
      (by simpa only [mul_comm] using h)

/-- The decimal cutoff n≥10^97826087 gives log n≥225000000.
Specialize the variable-exponent logarithm bound and compare rational constants. -/
theorem gaussianMR_log_cutoff {n : ℕ} (hn : 10 ^ 97826087 ≤ n) : (225000000 : ℝ) ≤ Real.log n := by
  have h := gaussianMR_log_of_decimal hn
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.Analysis
