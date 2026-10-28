/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseGrowth

/-! # One-ninth correction and inverse-cutoff growth -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At radii at least 64, the full correction is at most one ninth of the radius.
Use the tangent log bound also for its square, and a positive shifted polynomial. -/
theorem pointwiseCorrection_ninth {y : ℝ} (hy : 64 ≤ y) : pointwiseCorrection y ≤ y / 9 := by
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
    lowPrimeA y * (y / 64 + 16 / 5) ^ 2 + lowPrimeB y y * (y / 64 + 16 / 5) + lowPrimeC y y ≤
      (y / 9) * ((y - 1) * (y + 1) ^ 2) := by
    have he :
      (y / 9) * ((y - 1) * (y + 1) ^ 2) -
          (lowPrimeA y * (y / 64 + 16 / 5) ^ 2 + lowPrimeB y y * (y / 64 + 16 / 5) +
            lowPrimeC y y) =
        (1445 / 18432 : ℝ) * (y - 64) ^ 4 + (171042544289 / 10546560000 : ℝ) * (y - 64) ^ 3 +
          (586778115862519 / 527328000000 : ℝ) * (y - 64) ^ 2 +
          (278913475622239 / 10986000000 : ℝ) * (y - 64) +
          6681870479389 / 2059875000 := by
      dsimp only [lowPrimeA, lowPrimeB, lowPrimeC, lowPrimeV]
      ring
    nlinarith only [he, hu, pow_nonneg hu 2, pow_nonneg hu 3, pow_nonneg hu 4]
  have hd : (y - 1) * (y + 1) ^ 2 ≤ fullEndpointEvenGapDenominator y := by
    exact
      mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right
          (mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hy] : (0 : ℝ) ≤ y)) hz))
        (by linarith only [hy])
  have hd' := mul_le_mul_of_nonneg_left hd (by linarith only [hy] : (0 : ℝ) ≤ y / 9)
  have hzu : 0 ≤ y / 64 + 16 / 5 := by linarith only [hy]
  have hsq := (sq_le_sq₀ hz hzu).mpr (pointwise_log_upper hy)
  have hA := mul_le_mul_of_nonneg_left hsq ha
  have hB := mul_le_mul_of_nonneg_left (pointwise_log_upper hy) hb
  have hG := lowPrime_gap_quad hy0 y (Real.log y)
  have hEq := pointwiseGap_eq (L := y) hy8
  apply (mul_le_mul_iff_left₀ (fullEndpointEvenGapDenominator_pos hy8)).mp
  nlinarith only [hA, hB, hpoly, hd', hG, hEq]

/-- At levels at least 100 the inverse cutoff is at least 81 percent of the
level square. The inverse specification and one-ninth correction give the radius bound. -/
theorem pointwiseCutoff_lower81 {L : ℝ} (hL : 100 ≤ L) :
    (81 / 100 : ℝ) * L ^ 2 ≤ pointwiseCutoff L := by
  have hs := pointwiseRadius_spec L
  have hc := pointwiseCorrection_ninth (pointwiseRadius_sixtyFour hL)
  have hr : (9 / 10 : ℝ) * L ≤ pointwiseRadius L := by
    dsimp only [pointwiseLevel] at hs
    linarith only [hs.2.1, hc]
  have hsq :=
    (sq_le_sq₀ (by linarith only [hL] : (0 : ℝ) ≤ (9 / 10) * L)
          (by linarith only [hs.1] : (0 : ℝ) ≤ pointwiseRadius L)).mpr
      hr
  dsimp only [pointwiseCutoff]
  nlinarith only [hsq]

end PseudoPrime.LLS.PaperStatements
