/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeightUpper
public import PseudoPrime.Analysis.ExponentialFixedPointExecution
public import PseudoPrime.Analysis.ExponentialFixedPointConversions

/-! # Rational upper certificates for principal weights -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integer endpoints for a principal-weight upper certificate. The logarithm,
coordinate and square-root endpoints use thousandths; the exponential
denominator uses fixed-point scale one billion, and the weight uses millionths. -/
structure QuarterUpperWeightRow where
  cut : ℕ
  index : ℕ
  j : ℕ
  lo : ℤ
  hi : ℤ
  coordLo : ℤ
  coordHi : ℕ
  rootLo : ℕ
  expDen : ℕ
  weight : ℕ
  deriving DecidableEq

/-- Use the ratio at least one so that the rational logarithm series has a
suitable power-of-two normalization on either side of the cutoff. -/
def QuarterUpperWeightRow.logArg (r : QuarterUpperWeightRow) : ℚ :=
  if r.index ≤ r.cut then (r.cut : ℚ) / r.index else (r.index : ℚ) / r.cut

/-- The lower rational coordinate implied by the stored logarithm interval. -/
def QuarterUpperWeightRow.coordLowerBound (r : QuarterUpperWeightRow) : ℚ :=
  if r.index ≤ r.cut then 567 / 200 + (27 / 25 : ℚ) * (r.lo : ℚ) / 1000
  else 567 / 200 - (27 / 25 : ℚ) * (r.hi : ℚ) / 1000

/-- The upper rational coordinate implied by the stored logarithm interval. -/
def QuarterUpperWeightRow.coordUpperBound (r : QuarterUpperWeightRow) : ℚ :=
  if r.index ≤ r.cut then 567 / 200 + (27 / 25 : ℚ) * (r.hi : ℚ) / 1000
  else 567 / 200 - (27 / 25 : ℚ) * (r.lo : ℚ) / 1000

/-- Check the logarithm interval, coordinate and root bounds, the fixed-point
exponential denominator and the final rational weight inequality. -/
def QuarterUpperWeightRow.check (r : QuarterUpperWeightRow) : Bool :=
  Analysis.rationalLogIntervalCheck r.logArg r.j 32 ((r.lo : ℚ) / 1000) ((r.hi : ℚ) / 1000) &&
    decide
      (0 < r.index ∧
        0 < r.cut ∧
        0 < r.rootLo ∧
        0 < r.expDen ∧
        -(16000 : ℤ) ≤ r.coordLo ∧
        r.coordLo ≤ 16000 ∧
        (r.coordLo : ℚ) / 1000 ≤ r.coordLowerBound ∧
        r.coordUpperBound ≤ (r.coordHi : ℚ) / 1000 ∧
        ((r.rootLo : ℚ) / 1000) ^ 2 ≤ r.index ∧
        r.expDen ≤ Analysis.expFixedPointSignedLowerFast r.coordLo 1000 1000000000 32 ∧
        ((r.coordHi : ℚ) / 1000) ^ 5 * ((1000000000 : ℚ) / r.expDen) /
            (120 * ((r.rootLo : ℚ) / 1000)) ≤
          (r.weight : ℚ) / 1000000)

/-- A checked row bounds the actual principal scaled weight. The logarithm
interval controls the coordinate, the fixed-point lower exponential controls
its reciprocal, and the positive square-root endpoint controls division. -/
theorem QuarterUpperWeightRow.sound (r : QuarterUpperWeightRow) (hc : r.check = true) :
    refinedScaledWeight r.cut r.index ≤ (r.weight : ℝ) / 1000000 := by
  simp only [QuarterUpperWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨ht, hX, hR0, hD0, hlo, hhi, hcl, hcu, hroot, hden, hw⟩ := hc.2
  have htR : (0 : ℝ) < r.index := Nat.cast_pos.mpr ht
  have hXR : (0 : ℝ) < r.cut := Nat.cast_pos.mpr hX
  have hcoord :
    (r.coordLowerBound : ℝ) ≤ refinedCoord ((r.index : ℝ) / r.cut) ∧
      refinedCoord ((r.index : ℝ) / r.cut) ≤ (r.coordUpperBound : ℝ) := by
    by_cases hrev : r.index ≤ r.cut
    · have hlog := Analysis.rationalLogIntervalCheck_sound hc.1
      simp only [QuarterUpperWeightRow.logArg, ite_eq_left hrev, Rat.cast_div, Rat.cast_natCast,
        Rat.cast_intCast, Rat.cast_ofNat] at hlog
      have h := target028_scaled_coord_bounds htR hXR hlog.1 hlog.2
      simpa only [QuarterUpperWeightRow.coordLowerBound, QuarterUpperWeightRow.coordUpperBound,
        ite_eq_left hrev, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_intCast, mul_div_assoc] using h
    · have hlog := Analysis.rationalLogIntervalCheck_sound hc.1
      simp only [QuarterUpperWeightRow.logArg, ite_eq_right hrev, Rat.cast_div, Rat.cast_natCast,
        Rat.cast_intCast, Rat.cast_ofNat] at hlog
      simp only [QuarterUpperWeightRow.coordLowerBound, QuarterUpperWeightRow.coordUpperBound,
        ite_eq_right hrev, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_intCast]
      dsimp only [refinedCoord]
      constructor <;> linarith only [hlog.1, hlog.2]
  have hclR : (r.coordLo : ℝ) / 1000 ≤ refinedCoord ((r.index : ℝ) / r.cut) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcl
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat] at h
    exact h.trans hcoord.1
  have hcuR : refinedCoord ((r.index : ℝ) / r.cut) ≤ (r.coordHi : ℝ) / 1000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hcu
    simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at h
    exact hcoord.2.trans h
  have hrootR : (r.rootLo : ℝ) / 1000 ≤ Real.sqrt r.index := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg r.index)).mpr
    have h := (Rat.cast_le (K := ℝ)).mpr hroot
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow] using h
  have hloR : (-16000 : ℝ) ≤ r.coordLo := by exact_mod_cast hlo
  have hhiR : (r.coordLo : ℝ) ≤ 16000 := by exact_mod_cast hhi
  have habs : |(r.coordLo : ℝ)| ≤ 16000 := abs_le.mpr ⟨hloR, hhiR⟩
  have hsize : (|(((-(-r.coordLo) : ℤ) : ℝ))| / 1000) / (32 + 1 : ℕ) ≤ 1 / 2 := by
    simp only [neg_neg, Nat.cast_ofNat, Nat.reduceAdd]
    nlinarith only [habs]
  have hden' : r.expDen ≤ Analysis.expFixedPointSignedLower r.coordLo 1000 1000000000 32 := by
    simpa only [Analysis.expFixedPointSignedLowerFast_eq] using hden
  have hactual : 0 < Analysis.expFixedPointSignedLower r.coordLo 1000 1000000000 32 :=
    lt_of_lt_of_le hD0 hden'
  have hex :=
    Analysis.exp_upper_of_signed_fixed_lower (-r.coordLo) 1000 1000000000 32 (by decide) (by decide)
      hsize (by simpa only [neg_neg] using hactual)
  simp only [Int.cast_neg, neg_div, neg_neg, Nat.cast_ofNat] at hex
  have hdenR :
    (r.expDen : ℝ) ≤ (Analysis.expFixedPointSignedLower r.coordLo 1000 1000000000 32 : ℝ) :=
    Nat.cast_le.mpr hden'
  have hexR : Real.exp (-refinedCoord ((r.index : ℝ) / r.cut)) ≤ (1000000000 : ℝ) / r.expDen := by
    have hm :
      Real.exp (-refinedCoord ((r.index : ℝ) / r.cut)) ≤ Real.exp (-((r.coordLo : ℝ) / 1000)) :=
      Real.exp_le_exp.mpr (by linarith only [hclR])
    have hr :=
      div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 1000000000) (Nat.cast_pos.mpr hD0)
        hdenR
    exact hm.trans (hex.trans hr)
  have hwR := (Rat.cast_le (K := ℝ)).mpr hw
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_mul] at hwR
  exact
    (quarter_weight_upper_any hXR htR (by positivity) hcuR hexR (by positivity) hrootR).trans hwR

end PseudoPrime.PrimeTestBounds.MillerRabin
