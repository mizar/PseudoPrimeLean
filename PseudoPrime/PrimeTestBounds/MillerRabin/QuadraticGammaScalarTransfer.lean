/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCellTransfer
public import PseudoPrime.Analysis.RpowIntegerCertificate

/-! # Fixed-cell scalar certificates for the coupled Gamma comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive scale, a positive lower square-root endpoint and an upper
endpoint for x^(-9/16) bound all three positive Gamma error terms. Replace
the logarithmic parameter by the cell's nonnegative right endpoint before
bounding its denominator. This validates a whole cell from fixed scalars. -/
theorem gamma_cell_error_upper {x L H R W : ℝ} (hx : 0 < x) (hR : 0 < R) (hRs : R ^ 2 ≤ x)
    (hH : 0 ≤ H) (hLH : L ≤ H) (hW : x ^ (-9 / 16 : ℝ) ≤ W) :
    ((7 / 3 : ℝ) * L + 12) / Real.sqrt x + (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) ≤
      ((7 / 3 : ℝ) * H + 12) / R + (105 / 2 : ℝ) * W + 3 / (x * R) := by
  have hs := Real.le_sqrt_of_sq_le hRs
  have hnum : (0 : ℝ) ≤ (7 / 3 : ℝ) * H + 12 := by linarith only [hH]
  have hp :=
    (div_le_div_of_nonneg_right
          (show (7 / 3 : ℝ) * L + 12 ≤ (7 / 3 : ℝ) * H + 12 by linarith only [hLH])
          (Real.sqrt_nonneg x)).trans
      (div_le_div_of_nonneg_left hnum hR hs)
  have ht :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 3) (mul_pos hx hR)
      (mul_le_mul_of_nonneg_left hs hx.le)
  linarith only [hp, ht, hW]

/-- A fixed-cell scalar gap and actual principal/Euler/finite-main caps
reverse the coupled Gamma inequality for every parameter at most the cell's
right endpoint. All positive errors use certified square-root and rational
power endpoints. The conclusion feeds actual rejecting-prime extraction. -/
theorem gamma_gap_of_cell_caps (s : Finset ℕ) (x L H R W S U P : ℝ) (hx : 0 < x) (hR : 0 < R)
    (hRs : R ^ 2 ≤ x) (hH : 0 ≤ H) (hLH : L ≤ H) (hW : x ^ (-9 / 16 : ℝ) ≤ W)
    (hS : S ≤ ∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x)
    (hU : (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤ U)
    (hP : P ≤ ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k)
    (hE : (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) ≤ (3093 / 250 : ℝ))
    (hnum :
      U + 2 * (11783423 / 25000000 : ℝ) * H - 477 / 100 + (3093 / 250 - 4 * P) +
          ((7 / 3 : ℝ) * H + 12) / R +
          (105 / 2 : ℝ) * W +
          3 / (x * R) <
        4 * S) :
    (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) +
            2 * (11783423 / 25000000 : ℝ) * L -
          477 / 100 +
        ((∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) -
          4 * ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k) +
        ((7 / 3 : ℝ) * L + 12) / Real.sqrt x +
        (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
        3 / (x * Real.sqrt x) <
      4 * ∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x := by
  apply gamma_gap_of_numeric_bounds s x L S U P hS hU hP hE
  have he := gamma_cell_error_upper hx hR hRs hH hLH hW
  linarith only [hnum, he, hLH]

end PseudoPrime.PrimeTestBounds.MillerRabin
