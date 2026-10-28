/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseRoot
public import PseudoPrime.LLS.EndpointLowPrime

/-! # Coarse growth bounds for the pointwise inverse radius -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Above radius 64, a tangent logarithm bound is y/64+16/5. -/
theorem pointwise_log_upper {y : ℝ} (hy : 64 ≤ y) : Real.log y ≤ y / 64 + 16 / 5 := by
  have hp : 0 < y := by linarith only [hy]
  have h := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num only : (0 : ℝ) < 64))
  rw [Real.log_div hp.ne' (by norm_num only : (64 : ℝ) ≠ 0), show (64 : ℝ) = 2 ^ 6 by norm_num only,
    Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- Above radius 64 the pointwise correction is at most one quarter of the radius.
Bound the log square by y and the linear log by its tangent at 64. -/
theorem pointwiseCorrection_quarter {y : ℝ} (hy : 64 ≤ y) : pointwiseCorrection y ≤ y / 4 := by
  have hy8 : (8 : ℝ) ≤ y := by linarith only [hy]
  have hy0 : y ≠ 0 := ne_of_gt (by linarith only [hy])
  have hu : 0 ≤ y - 64 := sub_nonneg.mpr hy
  have hz : 0 ≤ Real.log y := Real.log_nonneg (by linarith only [hy])
  have ha : 0 ≤ lowPrimeA y := by
    dsimp only [lowPrimeA]
    nlinarith only [hy]
  have hb : 0 ≤ lowPrimeB y y := by
    have he :
      lowPrimeB y y =
        2 * (y - 64) ^ 3 + (17760380459 / 45775000 : ℝ) * (y - 64) ^ 2 +
          (143544281099 / 5721875 : ℝ) * (y - 64) +
          55681102897679 / 102993750 := by
      dsimp only [lowPrimeB, lowPrimeV]
      ring
    rw [he]
    nlinarith only [hu, pow_nonneg hu 2, pow_nonneg hu 3]
  have hpoly :
    lowPrimeA y * y + lowPrimeB y y * (y / 64 + 16 / 5) + lowPrimeC y y ≤
      (y / 4) * ((y - 1) * (y + 1) ^ 2) := by
    have he :
      (y / 4) * ((y - 1) * (y + 1) ^ 2) -
          (lowPrimeA y * y + lowPrimeB y y * (y / 64 + 16 / 5) + lowPrimeC y y) =
        (7 / 32 : ℝ) * (y - 64) ^ 4 + (27471632273 / 585920000 : ℝ) * (y - 64) ^ 3 +
          (6622088941313 / 1831000000 : ℝ) * (y - 64) ^ 2 +
          (3828634809571717 / 32958000000 : ℝ) * (y - 64) +
          2558079134489389 / 2059875000 := by
      dsimp only [lowPrimeA, lowPrimeB, lowPrimeC, lowPrimeV]
      ring
    nlinarith only [he, hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4]
  have hd : (y - 1) * (y + 1) ^ 2 ≤ fullEndpointEvenGapDenominator y := by
    exact
      mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hy] : (0 : ℝ) ≤ y)) hz))
        (by linarith only [hy])
  have hd' := mul_le_mul_of_nonneg_left hd (by linarith only [hy] : (0 : ℝ) ≤ y / 4)
  have hA := mul_le_mul_of_nonneg_left (log_sq_le_self_of_eight_le hy8) ha
  have hB := mul_le_mul_of_nonneg_left (pointwise_log_upper hy) hb
  have hG := lowPrime_gap_quad hy0 y (Real.log y)
  have hEq := pointwiseGap_eq (L := y) hy8
  apply (mul_le_mul_iff_left₀ (fullEndpointEvenGapDenominator_pos hy8)).mp
  nlinarith only [hA, hB, hpoly, hd', hG, hEq]

/-- For L>=100 the inverse radius is at least 64. -/
theorem pointwiseRadius_sixtyFour {L : ℝ} (hL : 100 ≤ L) : (64 : ℝ) ≤ pointwiseRadius L := by
  have hs := pointwiseRadius_spec L
  have h64 := pointwiseCorrection_quarter (by norm_num only : (64 : ℝ) ≤ 64)
  have hF64 : pointwiseLevel 64 ≤ 80 := by
    dsimp only [pointwiseLevel]
    linarith only [h64]
  rcases hs.2.2 with he | he
  · rw [he] at hs
    have h8 := pointwiseCorrection_eight_lt
    dsimp only [pointwiseLevel] at hs
    exfalso
    linarith only [hs.2.1, h8, hL]
  · by_contra hn
    have hm := pointwiseLevel_strictMonoOn hs.1 (by norm_num only : (8 : ℝ) ≤ 64) (lt_of_not_ge hn)
    rw [he] at hm
    linarith only [hm, hF64, hL]

/-- For L>=100 the inverse cutoff is at least (16/25)L^2. -/
theorem pointwiseCutoff_linear_lower {L : ℝ} (hL : 100 ≤ L) :
    (16 / 25 : ℝ) * L ^ 2 ≤ pointwiseCutoff L := by
  have hs := pointwiseRadius_spec L
  have hc := pointwiseCorrection_quarter (pointwiseRadius_sixtyFour hL)
  have hr : (4 / 5 : ℝ) * L ≤ pointwiseRadius L := by
    dsimp only [pointwiseLevel] at hs
    linarith only [hs.2.1, hc]
  have hsq :=
    (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ (4 / 5) * L)
          (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)).mpr
      hr
  dsimp only [pointwiseCutoff]
  nlinarith only [hsq]

/-- For L>=8 the inverse cutoff is strictly below L^2. -/
theorem pointwiseCutoff_lt_square {L : ℝ} (hL : 8 < L) : pointwiseCutoff L < L ^ 2 := by
  have hp := pointwiseCorrection_pos hL.le
  have hr : pointwiseRadius L < L :=
    pointwiseRadius_lt_of_level hL
      (by
        dsimp only [pointwiseLevel]; linarith only [hp])
  exact
    (sq_lt_sq₀ (by linarith only [(pointwiseRadius_spec L).1] : (0 : ℝ) ≤ pointwiseRadius L)
          (by linarith only [hL] : (0 : ℝ) ≤ L)).mpr
      hr

end PseudoPrime.LLS.PaperStatements
