/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainTail656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerEndpoints644
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiPrefix644
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Signed Euler tail at the section 132 left endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithm of ten bounds the RH error polynomial at one million. -/
private theorem euler_high_error_656 : eulerHighError656 1000000 ≤ 123 / 1000000 := by
  have hp : (1000000 : ℝ) ^ (-(11 / 10 : ℝ)) ≤ 251189 / 1000000000000 := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 11)
          (d := 10) (lo := 0) (hi := 251189 / 1000000000000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    linarith only [h]
  have hz : Real.log 1000000 ≤ 13816 / 1000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 10) (j := 3) (n := 16) (lo := 0) (hi :=
          23026 / 10000) (by decide +kernel)).2
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h
    rw [show (1000000 : ℝ) = 10 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [h]
  have h0 :=
    momentUpper 2 (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h1 :=
    momentUpper 3 (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  have h2 :=
    momentUpper 4 (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only : (1 : ℝ) ≤ 1000000) hp
      hz
  unfold eulerHighError656
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd] at h0 h1 h2
  linarith only [h0, h1, h2]

/-- A signed boundary lower bound and power-log upper enclosures give
an upper bound for the signed tail at a fixed endpoint. -/
private theorem signed_tail_box_656 {x z m e b : ℝ} (hx : 1 ≤ x) (hz : Real.log x ≤ z)
    (hm : x ^ (-(3 / 5) : ℝ) ≤ m) (he : x ^ (-(11 / 10) : ℝ) ≤ e) (hb : x ^ (-(8 / 5) : ℝ) ≤ b)
    (hψ : -70.4 ≤ Chebyshev.psi x - x) :
    signedTail656 x ≤
      3 / 8 * (m * Analysis.logPowerTailPoly (3 / 5) 0 z) +
        33 / 80 * (m * Analysis.logPowerTailPoly (3 / 5) 1 z) +
        121 / 800 * (m * Analysis.logPowerTailPoly (3 / 5) 2 z) +
        70.4 * (b * (3 / 8 + 33 / 80 * z + 121 / 800 * z ^ 2)) +
        (3 / 20 * (e * Analysis.logPowerTailPoly (11 / 10) 0 z) +
          143 / 500 * (e * Analysis.logPowerTailPoly (11 / 10) 1 z) +
          121 / 625 * (e * Analysis.logPowerTailPoly (11 / 10) 2 z)) +
        123 / 1000000 := by
  have hlog := Real.log_nonneg hx
  have hb₀ := (Real.rpow_nonneg (zero_le_one.trans hx) _).trans hb
  have hD : eulerDensity656 x ≤ b * (3 / 8 + 33 / 80 * z + 121 / 800 * z ^ 2) := by
    unfold eulerDensity656
    gcongr
  have hn : 0 ≤ eulerDensity656 x := by
    unfold eulerDensity656
    positivity
  unfold signedTail656 eulerMainTail656 eulerLowError656
  rw [sub_eq_add_neg, ← neg_mul]
  gcongr
  all_goals
    first
    | exact neg_le.mpr hψ
    | exact euler_high_error_656
    | exact momentUpper _ (by norm_num only) hx hm hz
    | exact momentUpper _ (by norm_num only) hx he hz

/-- The signed Euler tail at radius 322 is at most 0.053504, using
the shared signed Chebyshev bound and three certified powers. -/
theorem quarter_signed_tail_322_656 : signedTail656 (322 ^ 2) ≤ 0.053504 := by
  rw [show (322 : ℝ) ^ 2 = 103684 by norm_num only]
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 103684) (j := 17) (n := 24) (lo := 11) (hi :=
        11.549104) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 3) (d :=
        5) (lo := 0) (hi := 0.000978528) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000003038905) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 8) (d :=
        5) (lo := 0) (hi := 0.00000000943760) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hz hm he hb
  have h :=
    signed_tail_box_656 (by norm_num only) hz hm he hb
      (quarter_psi_signed_656 (by norm_num only) (by norm_num only))
  refine h.trans ?_
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd]

/-- The signed Euler tail at radius 325 is at most 0.053045, using
the shared signed Chebyshev bound and three certified powers. -/
theorem quarter_signed_tail_325_656 : signedTail656 (325 ^ 2) ≤ 0.053045 := by
  rw [show (325 : ℝ) ^ 2 = 105625 by norm_num only]
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 105625) (j := 17) (n := 24) (lo := 11) (hi :=
        11.567651) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 105625) (p := 3) (d :=
        5) (lo := 0) (hi := 0.000967699) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 105625) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000002977534) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 105625) (p := 8) (d :=
        5) (lo := 0) (hi := 0.00000000916165) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hz hm he hb
  have h :=
    signed_tail_box_656 (by norm_num only) hz hm he hb
      (quarter_psi_signed_656 (by norm_num only) (by norm_num only))
  refine h.trans ?_
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd]

end PseudoPrime.PrimeTestBounds.MillerRabin
