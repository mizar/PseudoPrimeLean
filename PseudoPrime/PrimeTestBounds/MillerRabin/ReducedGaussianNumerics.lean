/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedGaussianProfiles

/-! # Gaussian numeric budgets for reduced-contour profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gaussian scale is ten twenty-firsts of the profile cutoff at logarithmic scale `L`. -/
noncomputable def reducedGaussianScale (f : ReducedGaussianProfile) (L : ℝ) : ℝ :=
  (10 / 21 : ℝ) * f.C * L ^ 2
/-- The Gaussian scale is nonnegative for every real logarithmic scale. -/
theorem reducedGaussian_nonneg (f : ReducedGaussianProfile) (L : ℝ) :
    0 ≤ reducedGaussianScale f L := by
  dsimp only [reducedGaussianScale]
  exact mul_nonneg ((sq_nonneg f.gamma).trans f.lower) (sq_nonneg _)
/-- Above the entrance, the profile's lower slope bounds the square root of the scale. -/
theorem reducedGaussian_sqrt_lower (f : ReducedGaussianProfile) {L : ℝ} (hL : f.T ≤ L) :
    f.gamma * L ≤ Real.sqrt (reducedGaussianScale f L) := by
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have hg : 0 ≤ f.gamma := by linarith only [f.gammaLower]
  apply (Real.le_sqrt (mul_nonneg hg hL0) (reducedGaussian_nonneg f L)).mpr
  dsimp only [reducedGaussianScale]
  nlinarith only [mul_le_mul_of_nonneg_right f.lower (sq_nonneg L)]
/-- Above the entrance, the profile's upper bound controls the square root of the scale. -/
theorem reducedGaussian_sqrt_upper (f : ReducedGaussianProfile) {L : ℝ} (hL : f.T ≤ L) :
    Real.sqrt (reducedGaussianScale f L) ≤ (289 / 625 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num only) hL0
  · dsimp only [reducedGaussianScale]
    nlinarith only [mul_le_mul_of_nonneg_right f.upper (sq_nonneg L)]
/-- Above the entrance, the fourth root is bounded by `17 / 25` times `sqrt L`. -/
theorem reducedGaussian_fourth (f : ReducedGaussianProfile) {L : ℝ} (hL : f.T ≤ L) :
    reducedGaussianScale f L ^ (1 / 4 : ℝ) ≤ (17 / 25 : ℝ) * Real.sqrt L := by
  have he : reducedGaussianScale f L ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (reducedGaussianScale f L)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (reducedGaussian_nonneg f L)]
    norm_num only
  rw [he]
  convert Real.sqrt_le_sqrt (reducedGaussian_sqrt_upper f hL) using 1
  norm_num only [Real.sqrt_mul, Real.sqrt_div]
/-- Above the entrance, the scale exceeds `3 ^ 16`, enabling the ambient-error estimate. -/
theorem reducedGaussian_ge_three (f : ReducedGaussianProfile) {L : ℝ} (hL : f.T ≤ L) :
    (3 : ℝ) ^ 16 ≤ reducedGaussianScale f L := by
  have hs := reducedGaussian_sqrt_lower f hL
  have hg := mul_le_mul_of_nonneg_right f.gammaLower (show 0 ≤ L by linarith only [hL, f.entry])
  have hsq := Real.sq_sqrt (reducedGaussian_nonneg f L)
  have hp := Real.sqrt_nonneg (reducedGaussianScale f L)
  nlinarith only [hL, f.entry, hs, hg, hsq, hp,
    sq_nonneg (Real.sqrt (reducedGaussianScale f L) - f.gamma * L)]
/-- Above the entrance, an ambient error at most 30 satisfies the strict index-four budget. -/
theorem reducedGaussian_budget (f : ReducedGaussianProfile) {L E : ℝ} (hL : f.T ≤ L) (hE : E ≤ 30) :
    (161 / 200 : ℝ) * L + 70 * reducedGaussianScale f L ^ (1 / 4 : ℝ) + 3 * E <
      (21943 / 10000 : ℝ) * Real.sqrt (reducedGaussianScale f L) := by
  have hL0 : 0 ≤ L := by linarith only [hL, f.entry]
  have hv : f.v ^ 2 ≤ L := f.fourth.2.trans hL
  have hs : Real.sqrt L ≤ L / f.v := by
    apply (le_div_iff₀ f.fourth.1).2
    have hsq := Real.sq_sqrt hL0
    have hpos := mul_nonneg (Real.sqrt_nonneg L) f.fourth.1.le
    nlinarith only [hsq, hv, hpos, hL0]
  have hr := reducedGaussian_sqrt_lower f hL
  have hfour := reducedGaussian_fourth f hL
  let d := (21943 / 10000 : ℝ) * f.gamma - 161 / 200 - (70 * (17 / 25 : ℝ)) / f.v
  have hm : 90 < d * f.T := f.margin
  have hd : 0 < d := by
    have hT : 0 ≤ f.T := by linarith only [f.entry]
    by_contra hn
    have hh := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT
    linarith only [hm, hh]
  have hh := mul_le_mul_of_nonneg_left hL hd.le
  have hdL : 90 < d * L := hm.trans_le hh
  dsimp only [d] at hdL
  simp only [div_eq_mul_inv] at hs hdL
  nlinarith only [hdL, hr, hfour, hs, hE]
/-- If `log q ≤ L` above the entrance, the Gaussian ambient error is at most 30. -/
theorem reducedGaussian_ambient (f : ReducedGaussianProfile) {q : ℕ} {L : ℝ}
    (hL : f.T ≤ L) (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (reducedGaussianScale f L) ≤ 30 := by
  have hL0 : 0 < L := by linarith only [hL, f.entry]
  have hs := reducedGaussian_sqrt_lower f hL
  have hgamma := mul_le_mul_of_nonneg_right f.gammaLower hL0.le
  have hs0 : 0 < Real.sqrt (reducedGaussianScale f L) :=
    (mul_pos (by linarith only [f.gammaLower] : 0 < f.gamma) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (reducedGaussianScale f L)) ≤
      4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, f.entry, hq, hs, hgamma]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt (reducedGaussian_ge_three f hL)
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
    linarith only [Real.log_natCast_nonneg q]
  have hb := mul_le_mul_of_nonneg_left hdec hC
  have hB :
    (11 / 10 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) /
        (3 * Real.sqrt (reducedGaussianScale f L)) ≤
      4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs0)).mpr
    linarith only [hL, f.entry, hq, hs, hgamma]
  have hJ :
    (11 / 10 : ℝ) * reducedGaussianScale f L ^ (-9 / 16 : ℝ) *
        ((16 / 5) * (Real.log q + 283) + 5 / 3) ≤
      4 := by
    simp only [div_eq_mul_inv] at hb hB ⊢
    nlinarith only [hb, hB]
  dsimp only [LLS.PaperStatements.gaussianAmbientError]
  linarith only [hP, hJ]


end PseudoPrime.PrimeTestBounds.MillerRabin
