/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevRHError

/-! # Chebyshev estimates for LLS Euler blocks -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and `t ≥ 100000`, Chebyshev psi lies between `47t/50` and `53t/50`.
The three-quarter error and the rational fourth-root threshold `50/3` give
relative error at most `3/50`. This supplies positive Euler blocks without enumeration. -/
theorem psi_bounds_of_100000_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 100000 ≤ t) :
    (47 / 50 : ℝ) * t ≤ Chebyshev.psi t ∧ Chebyshev.psi t ≤ (53 / 50 : ℝ) * t := by
  have h :=
    AnalyticNumberTheory.Arithmetic.psi_error_le_div_of_fourth_power hRH (r := 50 / 3)
      (by norm_num only) (show (50 / 3 : ℝ) ^ 4 ≤ t by nlinarith only [ht])
  constructor <;> nlinarith only [(abs_le.mp h).1, (abs_le.mp h).2]

/-- Under RH and `a ≥ 10000`, the interval `(a, 5a/4]` has Mangoldt mass
at least `3a/100`. Apply the three-quarter error at both endpoints with
fourth-root thresholds `10` and `125/12`. This improves the positive Euler block. -/
theorem psi_five_fourths_block_lower (hRH : RiemannHypothesis) {a : ℝ} (ha : 10000 ≤ a) :
    3 * a / 100 ≤ Chebyshev.psi ((5 / 4 : ℝ) * a) - Chebyshev.psi a := by
  have h :=
    AnalyticNumberTheory.Arithmetic.psi_block_lower_of_fourth_powers hRH (a := a) (b := (5 / 4) * a)
      (r := 10) (s := 125 / 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only; exact ha)
      (by nlinarith only [ha] : (125 / 12 : ℝ) ^ 4 ≤ (5 / 4 : ℝ) * a)
  nlinarith only [h]

end PseudoPrime.LLS
