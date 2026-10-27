/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics

/-! # Gaussian MR error budgets with constant principal upper error -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L≥130000000, the MR scale exceeds 3¹⁶.
Compare squares to supply the existing left-moment decay range. -/
theorem gaussianMRScale_ge_three_pow_sixteen_principal {L : ℝ} (hL : 130000000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ gaussianMRScale L := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 130000000) hL 2
  dsimp only [gaussianMRScale]
  nlinarith only [hs]

/-- At L≥130000000 and log q≤L, the precise Gaussian ambient error
is at most 26. Bound its pole and left-moment terms by three each,
retaining the fixed zero and archimedean costs. -/
theorem gaussianMR_ambient_error_le_principal {q : ℕ} {L : ℝ} (hL : 130000000 ≤ L)
    (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMRScale L) ≤ 26 := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 130000000).trans_le hL
  have hs := gaussianMRScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (gaussianMRScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 69 / 125) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (gaussianMRScale L)) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (gaussianMRScale_ge_three_pow_sixteen_principal hL)
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

/-- At L≥130000000, sqrt(L)≤L/11400.
The square-root threshold 11400 and its exact square supply the error absorption. -/
theorem gaussianMR_sqrt_log_absorption_principal {L : ℝ} (hL : 130000000 ≤ L) :
    Real.sqrt L ≤ L / 11400 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 130000000).trans hL
  have hs : (11400 : ℝ) ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num only) hL0).mpr
      (by
        norm_num only; linarith only [hL])
  have hprod := mul_nonneg (Real.sqrt_nonneg L) (sub_nonneg.mpr hs)
  nlinarith only [hprod, Real.sq_sqrt hL0]

/-- At L≥130000000 and log q≤L, principal and secondary Gaussian errors
total at most L/800 after index normalization. Combine the fourth-root estimate
with the certified ambient error 26 and the square-root absorption. -/
theorem gaussianMR_error_budget_principal {q : ℕ} {L : ℝ} (hL : 130000000 ≤ L)
    (hq : Real.log q ≤ L) :
    (56 / 3 : ℝ) * gaussianMRScale L ^ (1 / 4 : ℝ) + 13 / 3 +
        LLS.PaperStatements.gaussianAmbientError q (gaussianMRScale L) ≤
      L / 800 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 130000000).trans hL
  have hfour := gaussianMRScale_fourth_root_le hL0
  have hs := gaussianMR_sqrt_log_absorption_principal hL
  have he := gaussianMR_ambient_error_le_principal hL hq
  nlinarith only [hfour, hs, he, hL]

end PseudoPrime.Analysis
