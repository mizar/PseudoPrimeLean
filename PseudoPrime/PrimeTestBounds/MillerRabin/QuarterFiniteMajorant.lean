/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredResidual
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredConstants

/-! # Rational majorants for finite uniform quarter budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `r ≥ 1`, logarithm and negative-power bounds give rational-ready
upper bounds for the reflected scale and moment in the finite quarter budget. -/
theorem quarter_finite_reflected_upper {r L P : ℝ} (hr : 1 ≤ r) (hlog : Real.log (r ^ 2) ≤ L)
    (hpow : (r ^ 2) ^ (-(27 / 25 : ℝ)) ≤ P) :
    quarterReflectedScale r ≤
        ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P * ((21 / 8 : ℝ) + L) ^ 5 ∧
      quarterMomentScale r ≤
        ((27 / 25 : ℝ) ^ 5 / 120) * (58721 / 1000000) * P *
          quarterMomentPolynomial ((21 / 8 : ℝ) + L) := by
  have hr2 : (1 : ℝ) ≤ r ^ 2 := by nlinarith only [hr]
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log (r ^ 2) := by
    have h := Real.log_nonneg hr2
    linarith only [h]
  have hz : (21 / 8 : ℝ) + Real.log (r ^ 2) ≤ (21 / 8 : ℝ) + L := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (58721 / 1000000 : ℝ) := by
    convert refined_exp_neg_unit_sharp using 1
    norm_num only
  have hp0 : 0 ≤ (r ^ 2) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (sq_nonneg r) _
  have hP0 : 0 ≤ P := hp0.trans hpow
  have hep := mul_le_mul he hpow hp0 (by norm_num only : (0 : ℝ) ≤ 58721 / 1000000)
  have hep0 : 0 ≤ (58721 / 1000000 : ℝ) * P := mul_nonneg (by norm_num only) hP0
  have h5 := pow_le_pow_left₀ hz0 hz 5
  have h5' := mul_le_mul hep h5 (pow_nonneg hz0 5) hep0
  have hpoly0 : 0 ≤ quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log (r ^ 2)) := by
    dsimp only [quarterMomentPolynomial]
    positivity
  have hpoly := quarter_moment_polynomial_le hz0 hz
  have hpoly' := mul_le_mul hep hpoly hpoly0 hep0
  have h5'' := mul_le_mul_of_nonneg_left h5' (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  have hpoly'' :=
    mul_le_mul_of_nonneg_left hpoly' (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  constructor
  · dsimp only [quarterReflectedScale]
    nlinarith only [h5'']
  · dsimp only [quarterMomentScale]
    nlinarith only [hpoly'']

end PseudoPrime.PrimeTestBounds.MillerRabin
