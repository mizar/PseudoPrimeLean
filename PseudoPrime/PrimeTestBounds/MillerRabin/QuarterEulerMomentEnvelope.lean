/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerIncrement
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTotal

/-! # Reusable rational lower envelope for Euler moments -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A lower envelope for the Euler moment increment from 1000 to a cutoff
with logarithm at most `L` and negative power at most `Q`. -/
noncomputable def quarterEulerMomentEnvelope (k : ℕ) (L Q : ℝ) : ℝ :=
  -(179 : ℝ) * (182 / 10000000 : ℝ) * (6907756 / 1000000 : ℝ) ^ k +
      (18197 / 1000000 : ℝ) * Analysis.logPowerTailPoly (29 / 50) k (6907755 / 1000000) -
    Q * Analysis.logPowerTailPoly (29 / 50) k L -
    (3 / 4 : ℝ) * (323596 / 100000000 : ℝ) *
      Analysis.logPowerTailPoly (83 / 100) k (6907756 / 1000000)

/-- Checked logarithm and negative-power endpoints bound the exact finite
moment increment below. The positive terminal correction is retained only by
its sign, while the fixed initial data use existing certificates. -/
theorem quarter_euler_moment_envelope (k : ℕ) {b L Q : ℝ} (hb : 1000 ≤ b) (hLB : Real.log b ≤ L)
    (hPB : b ^ (-(29 / 50 : ℝ)) ≤ Q) :
    quarterEulerMomentEnvelope k L Q ≤ quarterEulerMomentLower k b := by
  have hpA :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 1000 0 (323596 / 100000000) 83
              100 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hpA
  have hPA : (1000 : ℝ) ^ (-(83 / 100 : ℝ)) ≤ (323596 / 100000000 : ℝ) := by
    norm_num only at hpA ⊢
    exact hpA
  have hLA0 : 0 ≤ Real.log 1000 := Real.log_nonneg (by norm_num only)
  have hLB0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith only [hb])
  have hlow :=
    Analysis.log_power_tail_poly_mono (r := (29 / 50 : ℝ)) (by norm_num only)
      (show (0 : ℝ) ≤ 6907755 / 1000000 by norm_num only) refined_log_1000_lower k
  have hhighB :=
    Analysis.log_power_tail_poly_mono (r := (29 / 50 : ℝ)) (by norm_num only) hLB0 hLB k
  have hhighA :=
    Analysis.log_power_tail_poly_mono (r := (83 / 100 : ℝ)) (by norm_num only) hLA0
      refined_log_1000_upper k
  have hpolyL : 0 ≤ Analysis.logPowerTailPoly (29 / 50 : ℝ) k (6907755 / 1000000) :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only) (by norm_num only) k
  have hpolyB : 0 ≤ Analysis.logPowerTailPoly (29 / 50 : ℝ) k (Real.log b) :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only) hLB0 k
  have hpolyA : 0 ≤ Analysis.logPowerTailPoly (83 / 100 : ℝ) k (Real.log 1000) :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only) hLA0 k
  have hpos :=
    mul_le_mul refined_power_1000_bounds.1 hlow hpolyL
      (Real.rpow_nonneg (by norm_num only : (0 : ℝ) ≤ 1000) _)
  have hnegB :=
    mul_le_mul hPB hhighB hpolyB
      ((Real.rpow_nonneg (show (0 : ℝ) ≤ b by linarith only [hb]) _).trans hPB)
  have hnegA := mul_le_mul hPA hhighA hpolyA (by norm_num only : (0 : ℝ) ≤ 323596 / 100000000)
  have hs : Real.sqrt 1000 ≤ (31623 / 1000 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by norm_num only⟩
  have hss : Real.sqrt (Real.sqrt 1000) ≤ (5624 / 1000 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by norm_num only, hs.trans (by norm_num only)⟩
  have hroot : (1000 : ℝ) ^ (3 / 4 : ℝ) ≤ 179 := by
    rw [← quarter_sqrt_product (by norm_num only : (0 : ℝ) ≤ 1000)]
    have h := mul_le_mul hs hss (Real.sqrt_nonneg _) (by norm_num only : (0 : ℝ) ≤ 31623 / 1000)
    linarith only [h]
  have hweight :
    AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 1000 ≤
      (182 / 10000000 : ℝ) * (6907756 / 1000000 : ℝ) ^ k := by
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    exact
      mul_le_mul refined_power_1000_bounds.2.2.2.2.2
        (pow_le_pow_left₀ hLA0 refined_log_1000_upper k) (pow_nonneg hLA0 k)
        (by norm_num only : (0 : ℝ) ≤ 182 / 10000000)
  have hw0 : 0 ≤ AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 1000 := by
    dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    positivity
  have hboundary := mul_le_mul hroot hweight hw0 (by positivity : (0 : ℝ) ≤ 179)
  have hdrop :
    0 ≤ b ^ (-(83 / 100 : ℝ)) * Analysis.logPowerTailPoly (83 / 100 : ℝ) k (Real.log b) := by
    exact
      mul_nonneg (Real.rpow_nonneg (by linarith only [hb]) _)
        (Analysis.log_power_tail_poly_nonneg (by norm_num only) hLB0 k)
  dsimp only [quarterEulerMomentEnvelope, quarterEulerMomentLower, quarterEulerMomentIntegral]
  nlinarith only [hpos, hnegB, hnegA, hboundary, hdrop]

end PseudoPrime.PrimeTestBounds.MillerRabin
