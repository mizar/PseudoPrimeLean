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
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformNear200

/-! # Uniform Korselt interval from 398.5 to 398.75 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm and power checks cover the endpoints of radii 199.25
to 199.375. These finite checks certify the closed Euler tail throughout the interval. -/
private theorem quarter_euler_tail_19925_checks :
    Analysis.rationalLogIntervalCheck (2544025 / 64) 15 32 0 (10591 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (635209 / 16) 0 (21513 / 10000000)
          29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (635209 / 16) 0 (15241 / 100000000)
          83 100 =
        true := by
  decide +kernel

/-- For radii from 199.25 through 199.375, the closed Euler-tail envelope at the
squared radius is at most 11346/100000. Endpoint checks feed the monotone majorant. -/
private theorem quarter_euler_tail_19925_199375 {r : ℝ} (hlo : (797 / 4 : ℝ) ≤ r)
    (hhi : r ≤ (1595 / 8 : ℝ)) : quarterEulerClosedTailCap (r ^ 2) ≤ (11346 / 100000 : ℝ) := by
  have hlog := (Analysis.rationalLogIntervalCheck_sound quarter_euler_tail_19925_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_19925_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_19925_checks.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp hq
  have hmin : ((635209 / 16) : ℝ) ≤ r ^ 2 := by nlinarith only [hlo]
  have hmax : r ^ 2 ≤ ((2544025 / 64) : ℝ) := by nlinarith only [hlo, hhi]
  have hr0 : 0 < r ^ 2 := by nlinarith only [hlo]
  have hl : Real.log (r ^ 2) ≤ (10591 / 1000 : ℝ) := by
    have h := Real.log_le_log hr0 hmax
    norm_num only at hlog ⊢
    linarith only [h, hlog]
  have hP : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ (21513 / 10000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (635209 / 16)) hmin
        (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)
    norm_num only at hp ⊢
    linarith only [h, hp]
  have hQ : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ (15241 / 100000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (635209 / 16)) hmin
        (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)
    norm_num only at hq ⊢
    linarith only [h, hq]
  have h :=
    quarter_euler_closed_upper (X := r ^ 2) (L := 10591 / 1000) (P := 21513 / 10000000) (Q :=
      15241 / 100000000) (by nlinarith only [hlo]) hl (by norm_num only) (by norm_num only) hP hQ
  have hc :
    quarterEulerClosedUpper (10591 / 1000) (21513 / 10000000) (15241 / 100000000) ≤
      (11346 / 100000 : ℝ) := by
    norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  exact h.trans hc

/-- Rational logarithm and power checks at the lower radius endpoint. -/
private theorem quarter_negative_endpoint_19925_checks :
    Analysis.rationalLogIntervalCheck (635209 / 16) 15 32 0 (1058913 / 100000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (635209 / 16) 0
          (107970 / 10000000000) 27 25 =
        true := by
  decide +kernel

/-- The closed-tail residual satisfies the centered witness inequality on this radius interval. -/
private theorem quarter_scaled_residual_19925_199375 {r : ℝ} (hlo : (797 / 4 : ℝ) ≤ r)
    (hhi : r ≤ (1595 / 8 : ℝ)) :
    quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
        4 * quarterReflectedScale r -
        3 / 25 -
        7 / 250 -
        (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound quarter_negative_endpoint_19925_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_negative_endpoint_19925_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((797 / 4 : ℝ) ^ 2) ≤ (1058913 / 100000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((797 / 4 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (107970 / 10000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (141155 / 10000 : ℝ) ≤ Real.sqrt (797 / 4) := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt (1595 / 8) ≤ (141201 / 10000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := (797 / 4)) (b := (1595 / 8)) (L := 1058913 / 100000) (Q :=
      107970 / 10000000000) (s := 141155 / 10000) (t := 141201 / 10000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 11346 / 100000 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        (39 / 4000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        30 / 10000 +
        3 / 2000)
      (by norm_num only) hlo hhi hlog hpow (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_19925_199375 hlo (by linarith only [hhi])
  have hscale :=
    quarter_reflected_scale_lower_precise (by linarith only [hlo]) (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc, hscale]

/-- Under GRH, a uniform Korselt triple with logarithm in [398.5, 398.75]
has a rejecting prime below one quarter of the squared logarithm. -/
theorem quarter_uniform_3985_39875 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (797 / 2 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1595 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (797 / 4 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ (1595 / 8 : ℝ) := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_near200_scaled hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU]) hU
      hcut (quarter_scaled_residual_19925_199375 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin
