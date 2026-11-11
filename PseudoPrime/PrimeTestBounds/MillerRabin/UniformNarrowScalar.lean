/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformNarrowWitness

/-! # Endpoint transfer for arbitrary-cutoff narrow budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a logarithmic interval starting at 465, explicit endpoint bounds for the
reflected terms and roots imply the narrow scalar witness budget for `r = 52223 L / 100000`. -/
theorem uniform_narrow_scalar {a b L r R H J s t : ℝ} (ha : 465 ≤ a) (haL : a ≤ L) (hLb : L ≤ b)
    (hr : r = (52223 / 100000 : ℝ) * L) (hs : 0 < s) (hsqrt : s ≤ Real.sqrt r)
    (ht : Real.sqrt r ≤ t) (hR0 : 0 ≤ quarterReflectedScale r) (hR : quarterReflectedScale r ≤ R)
    (hH : quarterMomentScale r ≤ H) (hJ : quarterEulerClosedTailCap (r ^ 2) ≤ J)
    (hcert :
      (2645975208579 / 48828125000000000 : ℝ) * a +
            (27 / 25 : ℝ) ^ 5 *
              ((3117 / 400 : ℝ) - 7 / 200 - (351 / 200 : ℝ) / ((52223 / 100000 : ℝ) * a) -
                (529 / 5000 : ℝ) * t -
                (526064 / 10000000 : ℝ) / s) -
          (2 * b + 3 * (1839 / 1000 : ℝ)) * R -
          H -
          4 * J -
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 ≥
        0) :
    (2 * L) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 8 : ℝ) * L -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 *
          ((24439 / 50000 : ℝ) * r - (529 / 5000 : ℝ) * Real.sqrt r - 7 / 200 -
            (351 / 200 : ℝ) / r -
            (526064 / 10000000 : ℝ) / Real.sqrt r) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have ha0 : 0 < (52223 / 100000 : ℝ) * a := by nlinarith only [ha]
  have har : (52223 / 100000 : ℝ) * a ≤ r := by
    rw [hr]; nlinarith only [haL]
  have hb0 : 0 ≤ b := by linarith only [ha, haL, hLb]
  have hc := Analysis.log_two_mul_pi_lt
  have hcoef : 2 * L + 3 * Real.log (2 * Real.pi) ≤ 2 * b + 3 * (1839 / 1000 : ℝ) := by
    linarith only [hc, hLb]
  have hcoef0 : 0 ≤ 2 * b + 3 * (1839 / 1000 : ℝ) := by linarith only [hb0]
  have htR := mul_le_mul hcoef hR hR0 hcoef0
  have hinv := one_div_le_one_div_of_le ha0 har
  have hrootinv := one_div_le_one_div_of_le hs hsqrt
  have hlin :=
    mul_le_mul_of_nonneg_left haL
      (show (0 : ℝ) ≤ 2645975208579 / 48828125000000000 by norm_num only)
  have hd :=
    mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (351 / 200 : ℝ) by norm_num only)
  have hroot :=
    mul_le_mul_of_nonneg_left ht
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (529 / 5000 : ℝ) by norm_num only)
  have hinvs :=
    mul_le_mul_of_nonneg_left hrootinv
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (526064 / 10000000 : ℝ) by norm_num only)
  simp only [hr] at htR hH hJ hd hroot hinvs ⊢
  ring_nf at hcert htR hH hJ hlin hd hroot hinvs ⊢
  nlinarith only [hcert, htR, hH, hJ, hlin, hd, hroot, hinvs]

end PseudoPrime.PrimeTestBounds.MillerRabin
