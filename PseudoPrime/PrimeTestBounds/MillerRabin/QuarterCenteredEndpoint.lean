/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredResidual

/-! # Rational endpoint bounds for the centered residual -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational upper envelope for the centered residual. `L`, `Q`, and `s`
bound the cutoff logarithm, negative power, and square root respectively. -/
noncomputable def quarterCenteredEndpoint (a L Q s : ℝ) : ℝ :=
  (4 * a + 3 * (1839 / 1000 : ℝ)) *
      (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * Q * ((21 / 8 : ℝ) + L) ^ 5) +
    (((27 / 25 : ℝ) ^ 5 / 120) * (588 / 10000) * Q) * quarterMomentPolynomial ((21 / 8 : ℝ) + L) +
    (27 / 25 : ℝ) ^ 5 *
      ((6695 / 100000 : ℝ) + (29757 / 10000 : ℝ) / a + (526064 / 10000000 : ℝ) / s) +
    (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 +
    ((65 / 100 : ℝ) - 4 * (223 / 125 : ℝ)) * (27 / 25 : ℝ) ^ 5

/-- For a radius at least 34, verified endpoint bounds control the residual.
Each product is compared using nonnegativity, and reciprocal order reverses. -/
theorem quarter_centered_endpoint {a L Q s : ℝ} (ha : 34 ≤ a) (hlog : Real.log (a ^ 2) ≤ L)
    (hpow : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ Q) (hs : 0 < s) (hsqrt : s ≤ Real.sqrt a) :
    quarterCenteredResidual a ≤ quarterCenteredEndpoint a L Q s := by
  have ha0 : 0 < a := (by norm_num only : (0 : ℝ) < 34).trans_le ha
  have ha2 : (1 : ℝ) ≤ a ^ 2 := by nlinarith only [ha]
  have hl0 := Real.log_nonneg ha2
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log (a ^ 2) := by linarith only [hl0]
  have hz : (21 / 8 : ℝ) + Real.log (a ^ 2) ≤ (21 / 8 : ℝ) + L := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (588 / 10000 : ℝ) := by
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hq0 : 0 ≤ (a ^ 2) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (sq_nonneg a) _
  have hQ0 : 0 ≤ Q := hq0.trans hpow
  have hep := mul_le_mul he hpow hq0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hep0 : 0 ≤ (588 / 10000 : ℝ) * Q := mul_nonneg (by norm_num only) hQ0
  have hp := pow_le_pow_left₀ hz0 hz 5
  have hp' := mul_le_mul hep hp (pow_nonneg hz0 5) hep0
  have hpoly0 : 0 ≤ quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log (a ^ 2)) := by
    dsimp only [quarterMomentPolynomial]
    positivity
  have hpoly := quarter_moment_polynomial_le hz0 hz
  have hm := mul_le_mul hep hpoly hpoly0 hep0
  have hfirst :=
    mul_le_mul_of_nonneg_left hp'
      (show (0 : ℝ) ≤ (4 * a + 3 * (1839 / 1000 : ℝ)) * ((27 / 25 : ℝ) ^ 5 / 120) by positivity)
  have hsecond :=
    mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 / 120 by positivity)
  have hinv := one_div_le_one_div_of_le hs hsqrt
  have hroot :=
    mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (526064 / 10000000) by positivity)
  dsimp only [quarterCenteredResidual, quarterReflectedScale, quarterMomentScale,
    quarterCenteredEndpoint]
  ring_nf at hfirst hsecond hroot ⊢
  linarith only [hfirst, hsecond, hroot]

/-- A single rational endpoint comparison certifies the centered scalar gap
throughout `[a,b]`. The residual decreases, while the linear coefficient and
the negative square-root term attain their lower bounds at the upper endpoint. -/
theorem quarter_centered_gap_of_endpoint {a b r L Q s t : ℝ} (ha : 34 ≤ a) (har : a ≤ r)
    (hrb : r ≤ b) (hlog : Real.log (a ^ 2) ≤ L) (hpow : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ Q) (hs : 0 < s)
    (hsqrt : s ≤ Real.sqrt a) (ht : Real.sqrt b ≤ t)
    (hcert :
      quarterCenteredEndpoint a L Q s ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * b - (3 / 4 : ℝ) * b -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * t) :
    quarterCenteredResidual r ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hr : (34 : ℝ) ≤ r := ha.trans har
  have hres := quarter_centered_residual_antitone ha hr har
  have hend := quarter_centered_endpoint ha hlog hpow hs hsqrt
  have hlin :=
    mul_le_mul_of_nonpos_left hrb
      (show (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) - 3 / 4 ≤ 0 by norm_num only)
  have hroot :=
    mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hrb).trans ht)
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (108 / 1000) by norm_num only)
  linarith only [hres, hend, hlin, hroot, hcert]

/-- An improved Euler-prefix bound shifts the endpoint residual by a constant.
The same monotonicity argument certifies the shifted gap throughout `[a,b]`. -/
theorem quarter_centered_gap_of_prefix {a b r L Q s t P : ℝ} (ha : 34 ≤ a) (har : a ≤ r)
    (hrb : r ≤ b) (hlog : Real.log (a ^ 2) ≤ L) (hpow : (a ^ 2) ^ (-(27 / 25 : ℝ)) ≤ Q) (hs : 0 < s)
    (hsqrt : s ≤ Real.sqrt a) (ht : Real.sqrt b ≤ t)
    (hcert :
      quarterCenteredEndpoint a L Q s - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
        (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * b - (3 / 4 : ℝ) * b -
          (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * t) :
    quarterCenteredResidual r - 4 * (P - (223 / 125 : ℝ) * (27 / 25 : ℝ) ^ 5) ≤
      (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) * r - (3 / 4 : ℝ) * r -
        (27 / 25 : ℝ) ^ 5 * (108 / 1000 : ℝ) * Real.sqrt r := by
  have hr : (34 : ℝ) ≤ r := ha.trans har
  have hres := quarter_centered_residual_antitone ha hr har
  have hend := quarter_centered_endpoint ha hlog hpow hs hsqrt
  have hlin :=
    mul_le_mul_of_nonpos_left hrb
      (show (27 / 25 : ℝ) ^ 5 * (24439 / 50000 : ℝ) - 3 / 4 ≤ 0 by norm_num only)
  have hroot :=
    mul_le_mul_of_nonneg_left ((Real.sqrt_le_sqrt hrb).trans ht)
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (108 / 1000) by norm_num only)
  linarith only [hres, hend, hlin, hroot, hcert]

end PseudoPrime.PrimeTestBounds.MillerRabin
