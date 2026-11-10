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

/-! # Uniform Korselt interval from 397.25 to 397.75 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm and power checks cover the endpoints of radii 198.625
to 198.875. These finite checks certify the closed Euler tail throughout the interval. -/
private theorem quarter_euler_tail_198625_checks :
    Analysis.rationalLogIntervalCheck (2531281 / 64) 15 32 0 (10586 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2524921 / 64) 0 (21592 / 10000000)
          29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2524921 / 64) 0
          (15321 / 100000000) 83 100 =
        true := by
  decide +kernel

/-- For radii from 198.625 through 198.875, the closed Euler-tail envelope at the
squared radius is at most 11393/100000. Endpoint checks feed the monotone majorant. -/
private theorem quarter_euler_tail_198625_198875 {r : ℝ} (hlo : (1589 / 8 : ℝ) ≤ r)
    (hhi : r ≤ (1591 / 8 : ℝ)) : quarterEulerClosedTailCap (r ^ 2) ≤ (11393 / 100000 : ℝ) := by
  have hlog := (Analysis.rationalLogIntervalCheck_sound quarter_euler_tail_198625_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_198625_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_198625_checks.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp hq
  have hmin : ((2524921 / 64) : ℝ) ≤ r ^ 2 := by nlinarith only [hlo]
  have hmax : r ^ 2 ≤ ((2531281 / 64) : ℝ) := by nlinarith only [hlo, hhi]
  have hr0 : 0 < r ^ 2 := by nlinarith only [hlo]
  have hl : Real.log (r ^ 2) ≤ (10586 / 1000 : ℝ) := by
    have h := Real.log_le_log hr0 hmax
    norm_num only at hlog ⊢
    linarith only [h, hlog]
  have hP : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ (21592 / 10000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (2524921 / 64)) hmin
        (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)
    norm_num only at hp ⊢
    linarith only [h, hp]
  have hQ : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ (15321 / 100000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (2524921 / 64)) hmin
        (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)
    norm_num only at hq ⊢
    linarith only [h, hq]
  have h :=
    quarter_euler_closed_upper (X := r ^ 2) (L := 10586 / 1000) (P := 21592 / 10000000) (Q :=
      15321 / 100000000) (by nlinarith only [hlo]) hl (by norm_num only) (by norm_num only) hP hQ
  have hc :
    quarterEulerClosedUpper (10586 / 1000) (21592 / 10000000) (15321 / 100000000) ≤
      (11393 / 100000 : ℝ) := by
    norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  exact h.trans hc

/-- Rational logarithm and power checks at the lower radius endpoint. -/
private theorem quarter_negative_endpoint_198625_checks :
    Analysis.rationalLogIntervalCheck (2524921 / 64) 15 32 0 (105829 / 10000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (2524921 / 64) 0
          (108705 / 10000000000) 27 25 =
        true := by
  decide +kernel

/-- The closed-tail residual satisfies the centered witness inequality on this radius interval. -/
private theorem quarter_scaled_residual_198625_198875 {r : ℝ} (hlo : (1589 / 8 : ℝ) ≤ r)
    (hhi : r ≤ (1591 / 8 : ℝ)) :
    quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 -
        4 * quarterReflectedScale r -
        57 / 500 -
        7 / 250 -
        (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound quarter_negative_endpoint_198625_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_negative_endpoint_198625_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((1589 / 8 : ℝ) ^ 2) ≤ (105829 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((1589 / 8 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (108705 / 10000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (14093 / 1000 : ℝ) ≤ Real.sqrt (1589 / 8) := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt (1591 / 8) ≤ (14103 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := (1589 / 8)) (b := (1591 / 8)) (L := 105829 / 10000) (Q :=
      108705 / 10000000000) (s := 14093 / 1000) (t := 14103 / 1000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 11393 / 100000 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        (39 / 4000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
        19 / 10000)
      (by norm_num only) hlo hhi hlog hpow (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_198625_198875 hlo (by linarith only [hhi])
  have hscale := quarter_reflected_scale_lower (by linarith only [hlo]) (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc, hscale]

/-- Under GRH, a uniform Korselt triple with logarithm in [397.25, 397.75]
has a rejecting prime below one quarter of the squared logarithm. -/
theorem quarter_uniform_39725_39775 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (1589 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1591 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (1589 / 8 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ (1591 / 8 : ℝ) := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_residual_scaled hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut (quarter_scaled_residual_198625_198875 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin
