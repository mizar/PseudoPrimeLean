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

/-! # Uniform Korselt interval from 397 to 397.25 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The rational logarithm and power interval checks cover the endpoints of radii 198.5 to 198.625.
These finite checks are used to certify the closed Euler tail throughout that interval. -/
private theorem quarter_euler_tail_1985_checks :
    Analysis.rationalLogIntervalCheck (2524921 / 64) 15 32 0 (10584 / 1000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (157609 / 4) 0 (21608 / 10000000)
          29 50 =
        true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (157609 / 4) 0 (15337 / 100000000)
          83 100 =
        true := by
  decide +kernel

/-- For every radius from 198.5 through 198.625, the closed Euler-tail envelope at its square is at
most 11393/100000. Endpoint power and logarithm checks feed the common monotone majorant. -/
private theorem quarter_euler_tail_1985_198625 {r : ℝ} (hlo : (397 / 2 : ℝ) ≤ r)
    (hhi : r ≤ (1589 / 8 : ℝ)) : quarterEulerClosedTailCap (r ^ 2) ≤ (11393 / 100000 : ℝ) := by
  have hlog := (Analysis.rationalLogIntervalCheck_sound quarter_euler_tail_1985_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_1985_checks.2.1).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_euler_tail_1985_checks.2.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog hp hq
  have hmin : ((157609 / 4) : ℝ) ≤ r ^ 2 := by nlinarith only [hlo]
  have hmax : r ^ 2 ≤ ((2524921 / 64) : ℝ) := by nlinarith only [hlo, hhi]
  have hr0 : 0 < r ^ 2 := by nlinarith only [hlo]
  have hl : Real.log (r ^ 2) ≤ (10584 / 1000 : ℝ) := by
    have h := Real.log_le_log hr0 hmax
    norm_num only at hlog ⊢
    linarith only [h, hlog]
  have hP : (r ^ 2) ^ (-(29 / 50 : ℝ)) ≤ (21608 / 10000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (157609 / 4)) hmin
        (by norm_num only : (-(29 / 50 : ℝ)) ≤ 0)
    norm_num only at hp ⊢
    linarith only [h, hp]
  have hQ : (r ^ 2) ^ (-(83 / 100 : ℝ)) ≤ (15337 / 100000000 : ℝ) := by
    have h :=
      Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < (157609 / 4)) hmin
        (by norm_num only : (-(83 / 100 : ℝ)) ≤ 0)
    norm_num only at hq ⊢
    linarith only [h, hq]
  have h :=
    quarter_euler_closed_upper (X := r ^ 2) (L := 10584 / 1000) (P := 21608 / 10000000) (Q :=
      15337 / 100000000) (by nlinarith only [hlo]) hl (by norm_num only) (by norm_num only) hP hQ
  have hc :
    quarterEulerClosedUpper (10584 / 1000) (21608 / 10000000) (15337 / 100000000) ≤
      (11393 / 100000 : ℝ) := by
    norm_num only [quarterEulerClosedUpper, quarterMomentClosedUpper, Analysis.logPowerTailPoly]
  exact h.trans hc

/-- Rational logarithm and power checks at the lower radius endpoint. -/
private theorem quarter_negative_endpoint_1985_checks :
    Analysis.rationalLogIntervalCheck (157609 / 4) 15 32 0 (105816 / 10000) = true ∧
      AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck (157609 / 4) 0
          (108853 / 10000000000) 27 25 =
        true := by
  decide +kernel

/-- The closed-tail residual satisfies the centered witness inequality on this radius interval. -/
private theorem quarter_negative_residual_1985_198625 {r : ℝ} (hlo : (397 / 2 : ℝ) ≤ r)
    (hhi : r ≤ (1589 / 8 : ℝ)) :
    quarterCenteredClosedResidual r - (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 - 57 / 500 - 7 / 250 -
        (27 / 25 : ℝ) ^ 5 * (33 / 500) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hl := (Analysis.rationalLogIntervalCheck_sound quarter_negative_endpoint_1985_checks.1).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        quarter_negative_endpoint_1985_checks.2).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log ((397 / 2 : ℝ) ^ 2) ≤ (105816 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : ((397 / 2 : ℝ) ^ 2) ^ (-(27 / 25 : ℝ)) ≤ (108853 / 10000000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hs : (14089 / 1000 : ℝ) ≤ Real.sqrt (397 / 2) := Real.le_sqrt_of_sq_le (by norm_num only)
  have ht : Real.sqrt (1589 / 8) ≤ (14094 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have h :=
    quarter_centered_gap_first (a := (397 / 2)) (b := (1589 / 8)) (L := 105816 / 10000) (Q :=
      108853 / 10000000000) (s := 14089 / 1000) (t := 14094 / 1000) (P :=
      (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 - 11393 / 100000 + 7 / 1000 +
        (33 / 2000 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        (39 / 4000 : ℝ) * (27 / 25 : ℝ) ^ 2)
      (by norm_num only) hlo hhi hlog hpow (by norm_num only) hs ht
      (by norm_num only [quarterCenteredEndpoint, quarterMomentPolynomial])
  have hc := quarter_euler_tail_1985_198625 hlo (by linarith only [hhi])
  dsimp only [quarterCenteredClosedResidual, quarterCenteredResidual] at h ⊢
  linarith only [h, hc]

/-- Under GRH, a uniform Korselt triple with logarithm in [397, 397.25]
has a rejecting prime below one quarter of the squared logarithm. -/
theorem quarter_uniform_397_39725 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : (397 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (1589 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  let r : ℝ := Real.log n / 2
  have hr : (397 / 2 : ℝ) ≤ r := by
    dsimp only [r]; linarith only [hlo]
  have hrU : r ≤ (1589 / 8 : ℝ) := by
    dsimp only [r]; linarith only [hhi]
  have hU : Real.log n ≤ 2 * r := by
    dsimp only [r]; linarith only
  have hcut : r ^ 2 ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by
    dsimp only [r]
    ring_nf
    exact le_rfl
  exact
    quarter_uniform_residual_negative hn ho hu hGRH (by linarith only [hr]) (by linarith only [hrU])
      hU hcut (quarter_negative_residual_1985_198625 hr hrU)

end PseudoPrime.PrimeTestBounds.MillerRabin
