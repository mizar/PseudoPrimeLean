/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics

/-! # Relative-loss Gaussian MR numerical budgets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Normalize a relative Gaussian main term using any proved cutoff mass and
endpoint cap. The index, width, and retained mass stay as parameters so each
cutoff branch can specialize the same inequality. -/
theorem gaussianMR_normalized_main_lower_of_mass {m t s I E h M Ecap : ℝ} (hm : 4 ≤ m)
    (ht : t = m - 1) (hs : 0 < s) (hh : h = 1 / (3 * s)) (hh1 : h ≤ 1 / 2) (hI : M ≤ I)
    (hE : E ≤ Ecap) :
    ((m * M - Ecap) / t - (m * M) / (3 * t * s)) ≤ (m / t) * (1 - h) * I - E / t := by
  have htpos : 0 < t := by
    rw [ht]; linarith only [hm]
  have hm0 : 0 ≤ m := by linarith only [hm]
  have hfactor : 0 ≤ 1 - h := by linarith only [hh1]
  have hI' := mul_le_mul_of_nonneg_left hI (mul_nonneg hm0 hfactor)
  have hE' := neg_le_neg hE
  have hbase : m * (1 - h) * M - Ecap ≤ m * (1 - h) * I - E := by nlinarith only [hI', hE']
  calc
    _ = (m * (1 - h) * M - Ecap) / t := by
      rw [hh]
      field_simp [htpos.ne', hs.ne']
      ring_nf
    _ ≤ (m * (1 - h) * I - E) / t := div_le_div_of_nonneg_right hbase htpos.le
    _ = _ := by field_simp [htpos.ne']

/-- Convert a relative Gaussian subgroup inequality to its normalized scalar
budget for arbitrary cutoff mass, endpoint, index, conductor cost and radius.
The caller supplies the coefficient bounds and the final scalar contradiction;
this shared step handles normalization and the relative-width error terms. -/
theorem gaussianMR_relative_comparison_to_scalar {m t s r A L I E C h M Ecap conductor D beta : ℝ}
    (hm4 : 4 ≤ m) (ht : t = m - 1) (hs : 0 < s) (hr : r = s ^ 2) (hh : h = 1 / (3 * s))
    (hh1 : h ≤ 1 / 2) (hI : M ≤ I) (hE : E ≤ Ecap) (hC : C / t ≤ L) (hconductor : 0 ≤ conductor)
    (hD : D ≤ (m * M - Ecap) / t) (hbeta : (m / t) * (M / 3 + 3 / 10) ≤ beta)
    (hcmp :
      (m * (1 - h) * I - E) * r ≤
        conductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) + 13 + t * A)
    (hfinish :
      D * r ≤
          conductor * L + beta * s + (m / t) * (63 * Ecap / (10 * s) + 1839 * Ecap / (1000 * r)) +
            13 / t +
            A →
        False) :
    False := by
  have htpos : 0 < t := by
    rw [ht]
    linarith only [hm4]
  have hrpos : 0 < r := by
    rw [hr]
    exact sq_pos_of_pos hs
  have hmain := gaussianMR_normalized_main_lower_of_mass hm4 ht hs hh hh1 hI hE
  have hcmpDiv0 := div_le_div_of_nonneg_right hcmp htpos.le
  have hleftEq : ((m * (1 - h) * I - E) * r) / t = ((m / t) * (1 - h) * I - E / t) * r := by
    field_simp [htpos.ne']
  have hrightEq :
    (conductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) + 13 + t * A) /
        t =
      conductor * (C / t) + (m / t) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 / t +
        A := by
    field_simp [htpos.ne']
  have hW :
    1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E =
      3 * s / 10 + 63 * E / (10 * s) + 1839 * E / (1000 * r) := by
    rw [hh, hr]
    field_simp [hs.ne']
    ring
  have hcmpDiv :
    ((m / t) * (1 - h) * I - E / t) * r ≤
      conductor * (C / t) + (m / t) * (3 * s / 10 + 63 * E / (10 * s) + 1839 * E / (1000 * r)) +
        13 / t +
        A := by
    have hcmpDiv1 :
      ((m / t) * (1 - h) * I - E / t) * r ≤
        (conductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) + 13 +
            t * A) /
          t := by
      simpa only [hleftEq] using hcmpDiv0
    have hcmpDiv2 :
      ((m / t) * (1 - h) * I - E / t) * r ≤
        conductor * (C / t) + (m / t) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
          13 / t +
          A := by
      simpa only [hrightEq] using hcmpDiv1
    simpa only [hW] using hcmpDiv2
  have hratio0 : 0 ≤ m / t := by exact div_nonneg (by linarith only [hm4]) htpos.le
  have hCscaled := mul_le_mul_of_nonneg_left hC hconductor
  have hEterm1 : 63 * E / (10 * s) ≤ 63 * Ecap / (10 * s) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by positivity)
    · positivity
  have hEterm2 : 1839 * E / (1000 * r) ≤ 1839 * Ecap / (1000 * r) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by positivity)
    · positivity
  have hEterms := add_le_add hEterm1 hEterm2
  have hEtermsScaled := mul_le_mul_of_nonneg_left hEterms hratio0
  have hcmpUpper :
    conductor * (C / t) + (m / t) * (3 * s / 10 + 63 * E / (10 * s) + 1839 * E / (1000 * r)) +
        13 / t +
        A ≤
      conductor * L + (m / t) * (3 * s / 10 + 63 * Ecap / (10 * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    nlinarith only [hCscaled, hEtermsScaled]
  have hcombined := (mul_le_mul_of_nonneg_right hmain hrpos.le).trans (hcmpDiv.trans hcmpUpper)
  have hmainEq :
    ((m * M - Ecap) / t - (m * M) / (3 * t * s)) * r =
      ((m * M - Ecap) / t) * r - (m / t) * (M / 3) * s := by
    rw [hr]
    field_simp [htpos.ne', hs.ne']
  have hcombinedNorm :
    ((m * M - Ecap) / t) * r - (m / t) * (M / 3) * s ≤
      conductor * L + (m / t) * (3 * s / 10 + 63 * Ecap / (10 * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    simpa only [hmainEq] using hcombined
  have hDscaled := mul_le_mul_of_nonneg_right hD hrpos.le
  have hbetaScaled := mul_le_mul_of_nonneg_right hbeta hs.le
  have hfactor :
    (m / t) * (3 * s / 10) + (m / t) * (M / 3) * s = (m / t) * (M / 3 + 3 / 10) * s := by ring
  have hbudget :
    D * r ≤
      conductor * L + beta * s + (m / t) * (63 * Ecap / (10 * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    nlinarith only [hcombinedNorm, hDscaled, hbetaScaled, hfactor]
  exact hfinish hbudget

/-- For L at least 350000, the Gaussian MR scale exceeds 3^16.
Compare squared scales to enter the established left-moment decay range. -/
theorem gaussianMRScale_ge_three_pow_sixteen_relative {L : ℝ} (hL : 350000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ gaussianMRScale L := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 350000) hL 2
  dsimp only [gaussianMRScale]
  nlinarith only [hs]

/-- At L at least 350000 and log(q) at most L, the Gaussian ambient error
is at most 26. Bound the pole and left-moment contributions by three each. -/
theorem gaussianMR_ambient_error_le_relative {q : ℕ} {L : ℝ} (hL : 350000 ≤ L)
    (hq : Real.log q ≤ L) :
    LLS.PaperStatements.gaussianAmbientError q (gaussianMRScale L) ≤ 26 := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 350000).trans_le hL
  have hs := gaussianMRScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (gaussianMRScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 69 / 125) hL0).trans_le hs
  have hP :
    (2129 / 2000 : ℝ) * (((7 / 6) * Real.log q + 4) / Real.sqrt (gaussianMRScale L)) ≤ 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hs0]
    linarith only [hL, hq, hs]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_three_sqrt
      (gaussianMRScale_ge_three_pow_sixteen_relative hL)
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

/-- At L at least 350000, relative width 1/2000 gives lower error at most 201.
Use the scale square root and endpoint exponential bound before division. -/
theorem gaussianMR_relative_lower_error_le {L : ℝ} (hL : 350000 ≤ L) :
    1 / (10 * (1 / 2000 : ℝ)) +
        ((21 / (10 * (1 / 2000 : ℝ)) + 1839 / 1000) / Real.sqrt (gaussianMRScale L)) *
          Real.exp (1 / 16 : ℝ) ≤
      201 := by
  have hL0 : 0 < L := (by norm_num only : (0 : ℝ) < 350000).trans_le hL
  have hs := gaussianMRScale_sqrt_lower hL0.le
  have hs0 : 0 < Real.sqrt (gaussianMRScale L) :=
    (mul_pos (by norm_num only : (0 : ℝ) < 69 / 125) hL0).trans_le hs
  have he := gaussian_endpoint_exp_le
  have hmul :=
    mul_le_mul_of_nonneg_left he
      (by norm_num only : (0 : ℝ) ≤ 21 / (10 * (1 / 2000 : ℝ)) + 1839 / 1000)
  have hb :
    ((21 / (10 * (1 / 2000 : ℝ)) + 1839 / 1000) / Real.sqrt (gaussianMRScale L)) *
        Real.exp (1 / 16 : ℝ) ≤
      1 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hs0]
    linarith only [hmul, hs, hL]
  norm_num only at hb ⊢
  linarith only [hb]

/-- At L at least 350000, normalized conductor cost plus 300 is strictly
below the certified relative Gaussian main term. Use the rational square-root
lower bound and retain a strict margin for witness extraction. -/
theorem gaussianMR_relative_main_term_lt {L : ℝ} (hL : 350000 ≤ L) :
    (161 / 400 : ℝ) * L + 300 < (1827 / 2500 : ℝ) * Real.sqrt (gaussianMRScale L) := by
  have hs := gaussianMRScale_sqrt_lower ((by norm_num only : (0 : ℝ) ≤ 350000).trans hL)
  linarith only [hs, hL]

end PseudoPrime.Analysis
