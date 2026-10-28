/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics

/-! # Explicit Gaussian three-character branch numerics

The scale (2827/21000)L² gives cutoff (2827/10000)L² at lambda=21/10.
For L≥10¹² the unnormalized principal and secondary error is at most L/20000.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The Gaussian MR scale (2827/21000)L². Multiplying by cutoff 21/10 gives
(2827/10000)L². -/
noncomputable def gaussianNextTripleScale (L : ℝ) : ℝ :=
  (2827 / 21000 : ℝ) * L ^ 2

/-- The MR scale is nonnegative at every real logarithmic parameter.
The rational factor is positive and the remaining factor is a square. -/
theorem gaussianNextTripleScale_nonneg (L : ℝ) : 0 ≤ gaussianNextTripleScale L :=
  mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2827 / 21000) (sq_nonneg L)

/-- For L≥0 the scale square root is at least (1/3)L.
Compare squares with the exact rational scale coefficient. -/
theorem gaussianNextTripleScale_sqrt_lower {L : ℝ} (hL : 0 ≤ L) :
    (1 / 3 : ℝ) * L ≤ Real.sqrt (gaussianNextTripleScale L) := by
  apply (Real.le_sqrt (mul_nonneg (by norm_num only) hL) (gaussianNextTripleScale_nonneg L)).mpr
  dsimp only [gaussianNextTripleScale]
  nlinarith only [sq_nonneg L]

/-- For L≥0 the scale square root is at most (9/16)L.
Compare squares; this supplies the fourth-root upper bound. -/
theorem gaussianNextTripleScale_sqrt_upper {L : ℝ} (hL : 0 ≤ L) :
    Real.sqrt (gaussianNextTripleScale L) ≤ (9 / 16 : ℝ) * L := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) hL
  · dsimp only [gaussianNextTripleScale]
    nlinarith only [sq_nonneg L]

/-- For L≥0 the scale fourth root is at most (3/4)sqrt(L).
Identify the fourth root with the iterated square root and apply monotonicity. -/
theorem gaussianNextTripleScale_fourth_root_le {L : ℝ} (hL : 0 ≤ L) :
    gaussianNextTripleScale L ^ (1 / 4 : ℝ) ≤ (3 / 4 : ℝ) * Real.sqrt L := by
  have he :
    gaussianNextTripleScale L ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (gaussianNextTripleScale L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (gaussianNextTripleScale_nonneg L)]
    norm_num only
  rw [he]
  have h := Real.sqrt_le_sqrt (gaussianNextTripleScale_sqrt_upper hL)
  rw [Real.sqrt_mul (by norm_num only : (0 : ℝ) ≤ 9 / 16)] at h
  norm_num only [Real.sqrt_div] at h
  exact h

/-- For L≥225000000, the MR scale exceeds 3¹⁶.
Compare squares to supply the existing left-moment decay range. -/
theorem gaussianNextTripleScale_ge_three_pow_sixteen {L : ℝ} (hL : 225000000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ gaussianNextTripleScale L := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 225000000) hL 2
  dsimp only [gaussianNextTripleScale]
  nlinarith only [hs]

/-- At L≥225000000 and log q≤L, the precise Gaussian ambient error
is at most 2000. Bound its pole and left-moment terms by four each,
retaining the fixed zero and archimedean costs. -/
theorem gaussianNextTriple_ambient_error_le {q : ℕ} {L : ℝ} (hL : 225000000 ≤ L)
    (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianNextTripleScale L) ≤ 2000 := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 225000000).trans_le hL
  have hs := gaussianNextTripleScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (gaussianNextTripleScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 1 / 3) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (gaussianNextTripleScale L)) ≤
      4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (gaussianNextTripleScale_ge_three_pow_sixteen hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) /
        (3 * Real.sqrt (gaussianNextTripleScale L)) ≤
      4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, hq, hs]
  have hJ :
    (11 / 10 : ℝ) * gaussianNextTripleScale L ^ (-9 / 16 : ℝ) *
        ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      4 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]

/-- At L≥10¹², the actual unnormalized index-four error is at most L/20000.
Combine the fourth-root bound, fixed secondary allowance and square-root absorption. -/
theorem gaussianNextTriple_error_budget {q : ℕ} {L : ℝ} (hL : 2000000000000 ≤ L)
    (hq : Real.log q ≤ L) :
    70 * gaussianNextTripleScale L ^ (1 / 4 : ℝ) +
        3 * LLS.PaperStatements.gaussianAmbientError q (gaussianNextTripleScale L) ≤
      (1 / 10000 : ℝ) * L / 2 := by
  have hL0 : 0 ≤ L := (by norm_num only : (0 : ℝ) ≤ 2000000000000).trans hL
  have hfour := gaussianNextTripleScale_fourth_root_le hL0
  have hs : (1400000 : ℝ) ≤ Real.sqrt L :=
    (Real.le_sqrt (by norm_num only) hL0).mpr
      (by
        norm_num only; linarith only [hL])
  have hprod := mul_nonneg (Real.sqrt_nonneg L) (sub_nonneg.mpr hs)
  have habs : Real.sqrt L ≤ L / 1400000 := by nlinarith only [hprod, Real.sq_sqrt hL0]
  have hE :=
    gaussianNextTriple_ambient_error_le
      ((by norm_num only : (225000000 : ℝ) ≤ 2000000000000).trans hL) hq
  linarith only [hfour, habs, hE, hL]

end PseudoPrime.Analysis
