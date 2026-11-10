/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteRows
public import PseudoPrime.Analysis.ExponentialFixedPointExecution
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteGeneralWeight

/-! # Fine rational certificates for finite-cell weights -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational data for one endpoint weight: index and logarithm scale; integer
ten-thousandths for the logarithm bounds, coordinate upper bound, and square-root
upper bound; and fixed-point lower bounds for the exponential and weight. -/
structure QuarterFineWeightRow where
  cut : ℕ
  b : ℕ
  j : ℕ
  lo : ℤ
  hi : ℤ
  coord : ℕ
  root : ℕ
  exp : ℕ
  weight : ℕ
  deriving DecidableEq

/-- Rational lower coordinate associated with a checked endpoint row. -/
def QuarterFineWeightRow.lowerCoord (r : QuarterFineWeightRow) : ℚ :=
  567 / 200 + (27 / 25) * (r.lo : ℚ) / 10000

/-- The executable certificate for a finite-cutoff endpoint. Its checks cover
the logarithm interval, the coordinate and root bounds, the fixed-point
exponential, and the final rational weight comparison. -/
def QuarterFineWeightRow.check (r : QuarterFineWeightRow) : Bool :=
  Analysis.rationalLogIntervalCheck ((r.cut : ℚ) / (r.b : ℚ)) r.j 32 ((r.lo : ℚ) / 10000)
      ((r.hi : ℚ) / 10000) &&
    decide
      (0 < r.b ∧
        r.b ≤ r.cut ∧
        r.coord ≤ 160000 ∧
        0 ≤ r.lowerCoord ∧
        (567 / 200 : ℚ) + (27 / 25 : ℚ) * (r.hi : ℚ) / 10000 ≤ (r.coord : ℚ) / 10000 ∧
        (r.b : ℚ) ≤ ((r.root : ℚ) / 10000) ^ 2 ∧
        r.exp ≤ Analysis.expFixedPointSignedLowerFast (-(r.coord : ℤ)) 10000 1000000000 32 ∧
        (r.weight : ℚ) / 1000000 ≤
          r.lowerCoord ^ 5 * ((r.exp : ℚ) / 1000000000) / (120 * ((r.root : ℚ) / 10000)))

/-- A signed fixed-point exponential at ten-thousandth scale bounds the
actual negative exponential whenever the coordinate is below the endpoint. -/
theorem quarter_fine_exp_lower (u : ℕ) (hu : u ≤ 160000) {c : ℝ} (hc : c ≤ (u : ℝ) / 10000) :
    (Analysis.expFixedPointSignedLower (-(u : ℤ)) 10000 1000000000 32 : ℝ) / 1000000000 ≤
      Real.exp (-c) := by
  have hur : (u : ℝ) ≤ 160000 := by exact_mod_cast hu
  have hs : (|((-(u : ℤ) : ℤ) : ℝ)| / (10000 : ℝ)) / (32 + 1 : ℕ) ≤ 1 / 2 := by
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hur]
  have h :=
    Analysis.exp_fixed_signed_lower_div (-(u : ℤ)) 10000 1000000000 32 (by decide) (by decide) hs
  simp only [Int.cast_neg, Int.cast_natCast, Nat.cast_ofNat, neg_div] at h
  exact h.trans (Real.exp_le_exp.mpr (by linarith only [hc]))

/-- A successful endpoint check certifies its stated rational lower weight.
The logarithm and fixed-point exponential checkers provide analytic bounds;
the remaining comparisons are rational and transfer through the casts. -/
theorem QuarterFineWeightRow.sound (r : QuarterFineWeightRow) (hc : r.check = true) :
    (r.weight : ℝ) / 1000000 ≤ refinedScaledWeight r.cut r.b := by
  simp only [QuarterFineWeightRow.check, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hb, hb', hu, hL0, hU, hroot, hexp, hw⟩ := hc.2
  have hb0 : (0 : ℝ) < r.b := Nat.cast_pos.mpr hb
  have hbR : (r.b : ℝ) ≤ r.cut := by exact_mod_cast hb'
  have hX0 : (0 : ℝ) < r.cut := hb0.trans_le hbR
  have hlog := Analysis.rationalLogIntervalCheck_sound hc.1
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_intCast] at hlog
  have hcoord := target028_scaled_coord_bounds hb0 hX0 hlog.1 hlog.2
  have hL0R : (0 : ℝ) ≤ (r.lowerCoord : ℝ) := Rat.cast_nonneg.mpr hL0
  have hLR : (r.lowerCoord : ℝ) ≤ refinedCoord ((r.b : ℝ) / r.cut) := by
    simpa only [QuarterFineWeightRow.lowerCoord, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_intCast, mul_div_assoc] using hcoord.1
  have hUR : refinedCoord ((r.b : ℝ) / r.cut) ≤ (r.coord : ℝ) / 10000 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hU
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast,
      Rat.cast_natCast] at h
    linarith only [hcoord.2, h]
  have hrootR : Real.sqrt r.b ≤ (r.root : ℝ) / 10000 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · have h := (Rat.cast_le (K := ℝ)).mpr hroot
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow] using h
  have he :
    (r.exp : ℝ) ≤ (Analysis.expFixedPointSignedLower (-(r.coord : ℤ)) 10000 1000000000 32 : ℝ) := by
    exact Nat.cast_le.mpr (by simpa only [Analysis.expFixedPointSignedLowerFast_eq] using hexp)
  have heR : (r.exp : ℝ) / 1000000000 ≤ Real.exp (-refinedCoord ((r.b : ℝ) / r.cut)) := by
    exact
      (div_le_div_of_nonneg_right he (by norm_num only)).trans
        (quarter_fine_exp_lower r.coord hu hUR)
  have hwR := (Rat.cast_le (K := ℝ)).mpr hw
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow, Rat.cast_mul] at hwR
  exact
    hwR.trans
      (target028_scaled_weight_lower hb0 hbR hL0R hLR
        (div_nonneg (Nat.cast_nonneg r.exp) (by norm_num only)) heR hrootR)

end PseudoPrime.PrimeTestBounds.MillerRabin
