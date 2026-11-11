/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredResidual
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTailInterval

/-! # Endpoint transfer for finite uniform quarter budgets -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a positive radius interval, upper bounds for the reflected scale, moment
and Euler tail reduce the finite quarter budget to a rational endpoint inequality. -/
theorem quarter_finite_budget_of_bounds {a b r R H J : ℝ} (ha : 0 < a) (har : a ≤ r) (hrb : r ≤ b)
    (hR0 : 0 ≤ quarterReflectedScale r) (hR : quarterReflectedScale r ≤ R)
    (hH : quarterMomentScale r ≤ H) (hJ : quarterEulerClosedTailCap (r ^ 2) ≤ J)
    (hcert :
      (27 / 25 : ℝ) ^ 5 * ((3117 / 400 : ℝ) - 7 / 200 - (29631 / 200 : ℝ) / a) -
          (15537999327 / 488281250000 : ℝ) * b -
          (4 * b + 3 * (1839 / 1000 : ℝ)) * R -
          H -
          4 * J -
          (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 ≥
        0) :
    (4 * r) * quarterReflectedScale r + (39 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 + quarterMomentScale r +
            (3 / 4 : ℝ) * r -
          (3117 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 +
        4 * quarterEulerClosedTailCap (r ^ 2) ≤
      (27 / 25 : ℝ) ^ 5 * ((24439 / 50000 : ℝ) * r - 7 / 200 - (29631 / 200 : ℝ) / r) -
        3 * Real.log (2 * Real.pi) * quarterReflectedScale r := by
  have hr0 : 0 < r := ha.trans_le har
  have hb0 : 0 ≤ b := (le_of_lt hr0).trans hrb
  have hc := Analysis.log_two_mul_pi_lt
  have hcoef : 4 * r + 3 * Real.log (2 * Real.pi) ≤ 4 * b + 3 * (1839 / 1000 : ℝ) := by
    linarith only [hc, hrb]
  have hcoef0 : 0 ≤ 4 * b + 3 * (1839 / 1000 : ℝ) := by linarith only [hb0]
  have ht := mul_le_mul hcoef hR hR0 hcoef0
  have hinv := one_div_le_one_div_of_le ha har
  have hk : (0 : ℝ) ≤ 15537999327 / 488281250000 := by norm_num only
  have hlin := mul_le_mul_of_nonneg_left hrb hk
  have hd :=
    mul_le_mul_of_nonneg_left hinv
      (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 * (29631 / 200 : ℝ) by norm_num only)
  ring_nf at hcert ht hlin hd ⊢
  nlinarith only [hcert, ht, hH, hJ, hlin, hd]

end PseudoPrime.PrimeTestBounds.MillerRabin
