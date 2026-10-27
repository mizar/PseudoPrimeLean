/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMRNumerics

/-! # Relative Gaussian MR scalar normalization with arbitrary positive width factor -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a certified cutoff mass, endpoint cap and width h=k/s, normalize the Gaussian main
term by the positive index excess. Only h<=1/2 is needed here; k enters algebraically.
This is the common mass-normalization input for variable-width MR budgets. -/
theorem gaussianMR_main_lower_width {m t s I E h M Ecap k : ℝ} (hm : 4 ≤ m)
    (ht : t = m - 1) (hs : 0 < s) (hh : h = k / s) (hh1 : h ≤ 1 / 2) (hI : M ≤ I)
    (hE : E ≤ Ecap) :
    ((m * M - Ecap) / t - (m * M) * k / (t * s)) ≤ (m / t) * (1 - h) * I - E / t := by
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
      field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | norm_num only)
      ring_nf
    _ ≤ (m * (1 - h) * I - E) / t := div_le_div_of_nonneg_right hbase htpos.le
    _ = _ := by field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | norm_num only)

/-- Convert a relative Gaussian subgroup inequality to its normalized scalar
budget for arbitrary cutoff mass, endpoint, index, conductor cost and radius.
The caller supplies the coefficient bounds and the final scalar contradiction;
this shared step handles normalization and the relative-width error terms. -/
theorem gaussianMR_compare_width {m t s r A L I E C h M Ecap conductor D beta k : ℝ}
    (hk : 0 < k)
    (hm4 : 4 ≤ m) (ht : t = m - 1) (hs : 0 < s) (hr : r = s ^ 2) (hh : h = k / s)
    (hh1 : h ≤ 1 / 2) (hI : M ≤ I) (hE : E ≤ Ecap) (hC : C / t ≤ L) (hconductor : 0 ≤ conductor)
    (hD : D ≤ (m * M - Ecap) / t) (hbeta : (m / t) * (M * k + 1 / (10 * k)) ≤ beta)
    (hcmp :
      (m * (1 - h) * I - E) * r ≤
        conductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) + 13 + t * A)
    (hfinish :
      D * r ≤
          conductor * L + beta * s +
            (m / t) * (21 * Ecap / (10 * k * s) + 1839 * Ecap / (1000 * r)) +
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
  have hmain := gaussianMR_main_lower_width hm4 ht hs hh hh1 hI hE
  have hcmpDiv0 := div_le_div_of_nonneg_right hcmp htpos.le
  have hleftEq : ((m * (1 - h) * I - E) * r) / t = ((m / t) * (1 - h) * I - E / t) * r := by
    field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | exact hk.ne'
      | norm_num only)
  have hrightEq :
    (conductor * C + m * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) + 13 + t * A) /
        t =
      conductor * (C / t) +
        (m / t) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
        13 / t +
        A := by
    field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | exact hk.ne'
      | norm_num only)
  have hW :
    1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E =
      s / (10 * k) + 21 * E / (10 * k * s) + 1839 * E / (1000 * r) := by
    rw [hh, hr]
    field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | exact hk.ne'
      | norm_num only)
    ring
  have hcmpDiv :
    ((m / t) * (1 - h) * I - E / t) * r ≤
      conductor * (C / t) +
        (m / t) * (s / (10 * k) + 21 * E / (10 * k * s) + 1839 * E / (1000 * r)) +
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
        conductor * (C / t) +
        (m / t) * (1 / (10 * h) + ((21 / (10 * h) + 1839 / 1000) / r) * E) +
          13 / t +
          A := by
      simpa only [hrightEq] using hcmpDiv1
    simpa only [hW] using hcmpDiv2
  have hratio0 : 0 ≤ m / t := by exact div_nonneg (by linarith only [hm4]) htpos.le
  have hCscaled := mul_le_mul_of_nonneg_left hC hconductor
  have hEterm1 : 21 * E / (10 * k * s) ≤ 21 * Ecap / (10 * k * s) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
    · exact mul_nonneg (mul_nonneg (by norm_num only) hk.le) hs.le
  have hEterm2 : 1839 * E / (1000 * r) ≤ 1839 * Ecap / (1000 * r) := by
    apply div_le_div_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left hE (by norm_num only)
    · exact mul_nonneg (by norm_num only) hrpos.le
  have hEterms := add_le_add hEterm1 hEterm2
  have hEtermsScaled := mul_le_mul_of_nonneg_left hEterms hratio0
  have hcmpUpper :
    conductor * (C / t) +
        (m / t) * (s / (10 * k) + 21 * E / (10 * k * s) + 1839 * E / (1000 * r)) +
        13 / t +
        A ≤
      conductor * L +
        (m / t) * (s / (10 * k) + 21 * Ecap / (10 * k * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    nlinarith only [hCscaled, hEtermsScaled]
  have hcombined := (mul_le_mul_of_nonneg_right hmain hrpos.le).trans (hcmpDiv.trans hcmpUpper)
  have hmainEq :
    ((m * M - Ecap) / t - (m * M) * k / (t * s)) * r =
      ((m * M - Ecap) / t) * r - (m / t) * (M * k) * s := by
    rw [hr]
    field_simp (disch := first
      | exact htpos.ne'
      | exact hs.ne'
      | exact hk.ne'
      | norm_num only)
  have hcombinedNorm :
    ((m * M - Ecap) / t) * r - (m / t) * (M * k) * s ≤
      conductor * L +
        (m / t) * (s / (10 * k) + 21 * Ecap / (10 * k * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    simpa only [hmainEq] using hcombined
  have hDscaled := mul_le_mul_of_nonneg_right hD hrpos.le
  have hbetaScaled := mul_le_mul_of_nonneg_right hbeta hs.le
  have hfactor :
    (m / t) * (s / (10 * k)) + (m / t) * (M * k) * s =
       (m / t) * (M * k + 1 / (10 * k)) * s := by ring
  have hbudget :
    D * r ≤
      conductor * L + beta * s +
            (m / t) * (21 * Ecap / (10 * k * s) + 1839 * Ecap / (1000 * r)) +
        13 / t +
        A := by
    nlinarith only [hcombinedNorm, hDscaled, hbetaScaled, hfactor]
  exact hfinish hbudget


end PseudoPrime.Analysis
