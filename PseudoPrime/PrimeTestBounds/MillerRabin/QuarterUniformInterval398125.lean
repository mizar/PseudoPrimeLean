/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailInterval
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredFirstEndpoint
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosedNegative

/-! # Uniform Korselt interval from 398 to 398.125 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm and power checks cover the endpoints of radii 198.875
to 199. These finite checks certify the closed Euler tail throughout the interval. -/
private theorem quarter_euler_tail_199_checks :
    Analysis.rationalLogIntervalCheck (10144225 / 256) 15 32 0 (10588 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 39601 0 (21545 / 10000000) 29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 39601 0 (15274 / 100000000) 83
          100 =
        true := by
  decide +kernel

/-- For radii from 199 through 199.0625, the closed Euler-tail envelope at the
squared radius is at most 11359/100000. Endpoint checks feed the monotone majorant. -/
private theorem quarter_euler_tail_199_1990625 {r : ℝ} (hlo : (199 : ℝ) ≤ r)
    (hhi : r ≤ (3185 / 16 : ℝ)) : quarterEulerClosedTailCap (r ^ 2) ≤ (11359 / 100000 : ℝ) := by
  have hlog := (Analysis.rationalLogIntervalCheck_sound quarter_euler_tail_199_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_199_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_199_checks.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp hq
  have hmin : (39601 : ℝ) ≤ r ^ 2 := by nlinarith only [hlo]
  have hmax : r ^ 2 ≤ ((10144225 / 256) : ℝ) := by nlinarith only [hlo, hhi]
  have hr0 : 0 < r ^ 2 := by nlinarith only [hlo]
  have hl : Real.log (r ^ 2) ≤ (10588 / 1000 : ℝ) := by
    have h := Real.log_le_log hr0 hmax
    norm_num only at hlog ⊢
    linarith only [h, hlog]
  have hP : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ (21545 / 10000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 39601) hmin
        (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)
    norm_num only at hp ⊢
    linarith only [h, hp]
  have hQ : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ (15274 / 100000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 39601) hmin
        (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)
    norm_num only at hq ⊢
    linarith only [h, hq]
  have h :=
    quarter_euler_closed_upper (X := r ^ 2) (L := 10588 / 1000) (P := 21545 / 10000000) (Q :=
      15274 / 100000000) (by nlinarith only [hlo]) hl (by norm_num only) (by norm_num only) hP hQ
  have hc :
    quarterEulerClosedUpper (10588 / 1000) (21545 / 10000000) (15274 / 100000000) ≤
      (11359 / 100000 : ℝ) := by
    norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  exact h.trans hc

/-- Rational logarithm and power checks at the lower radius endpoint. -/
private theorem quarter_negative_endpoint_199_checks :
    Analysis.rationalLogIntervalCheck 39601 15 32 0 (105867 / 10000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 39601 0 (108263 / 10000000000) 27
          25 =
        true := by
  decide +kernel

/-- The closed-tail residual satisfies the centered witness inequality on this radius interval. -/
private theorem quarter_scaled_residual_199_1990625 {r : ℝ} (hlo : (199 : ℝ) ≤ r)
    (hhi : r ≤ (3185 / 16 : ℝ)) :
    quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
        4 * quarterReflectedScale r -
        57 / 500 -
        7 / 250 -
        (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound quarter_negative_endpoint_199_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_negative_endpoint_199_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((199 : ℝ) ^ 2) ≤ (105867 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((199 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (108263 / 10000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (14106 / 1000 : ℝ) ≤ Real.sqrt 199 := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt (3185 / 16) ≤ (14109 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := 199) (b := (3185 / 16)) (L := 105867 / 10000) (Q :=
      108263 / 10000000000) (s := 14106 / 1000) (t := 14109 / 1000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 11359 / 100000 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        (39 / 4000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        24 / 10000)
      (by norm_num only) hlo hhi hlog hpow (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_199_1990625 hlo (by linarith only [hhi])
  have hscale :=
    quarter_reflected_scale_lower_sharp (by linarith only [hlo]) (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc, hscale]

/-- Under GRH, a uniform Korselt triple with logarithm in [398, 398.125]
has a rejecting prime below one quarter of the squared logarithm. -/
theorem quarter_uniform_398_398125 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (398 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3185 / 8 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (199 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ (3185 / 16 : ℝ) := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_residual_scaled hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut (quarter_scaled_residual_199_1990625 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin
