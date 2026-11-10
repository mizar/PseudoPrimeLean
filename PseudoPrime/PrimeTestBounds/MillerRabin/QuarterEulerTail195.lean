/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailInterval
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedBounds
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! Euler tail interval certificate for radii 195 through 197. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm and power interval checks cover the endpoints of radii 195 to 197.
These finite checks are used to certify the closed Euler tail throughout that interval. -/
theorem quarter_euler_tail_195_checks :
    Analysis.rationalLogIntervalCheck 38809 15 32 0 (10567 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 38025 0 (2206 / 1000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 38025 0 (15796 / 100000000) 83
          100 =
        true := by
  decide +kernel

/-- For every radius from 195 through 197, the closed Euler-tail envelope at its square is at
most 117/1000. Endpoint power and logarithm checks feed the common monotone majorant. -/
theorem quarter_euler_tail_195_197 {r : ℝ} (hlo : 195 ≤ r) (hhi : r ≤ 197) :
    quarterEulerClosedTailCap (r ^ 2) ≤ (117 / 1000 : ℝ) := by
  have hlog := (Analysis.rationalLogIntervalCheck_sound quarter_euler_tail_195_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_195_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_195_checks.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp hq
  have hmin : (38025 : ℝ) ≤ r ^ 2 := by nlinarith only [hlo]
  have hmax : r ^ 2 ≤ (38809 : ℝ) := by nlinarith only [hlo, hhi]
  have hr0 : 0 < r ^ 2 := by nlinarith only [hlo]
  have hl : Real.log (r ^ 2) ≤ (10567 / 1000 : ℝ) := by
    have h := Real.log_le_log hr0 hmax
    norm_num only at hlog ⊢
    linarith only [h, hlog]
  have hP : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ (2206 / 1000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 38025) hmin
        (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)
    norm_num only at hp ⊢
    linarith only [h, hp]
  have hQ : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ (15796 / 100000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 38025) hmin
        (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)
    norm_num only at hq ⊢
    linarith only [h, hq]
  have h :=
    quarter_euler_closed_upper (X := r ^ 2) (L := 10567 / 1000) (P := 2206 / 1000000) (Q :=
      15796 / 100000000) (by nlinarith only [hlo]) hl (by norm_num only) (by norm_num only) hP hQ
  have hc :
    quarterEulerClosedUpper (10567 / 1000) (2206 / 1000000) (15796 / 100000000) ≤
      (117 / 1000 : ℝ) := by
    norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  exact h.trans hc

end PseudoPrime.PrimeTestBounds.MillerRabin
