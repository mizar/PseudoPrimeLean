/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticMain

/-! # Rational-cap interface for analytic Gamma cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A finite set of upper caps turns the analytic Gamma lower estimate into
any proposed scalar lower cap. Nonnegative intermediate allowances permit
monotone replacement of the exponential and square-root denominators. This
separates exact rational cell checks from the RH-dependent analytic proof. -/
theorem finite_gamma_lower_of_caps (hRH : RiemannHypothesis) {x y h r e p s z F : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hcut : 1 < x * y) (hh : 0 < h) (hh1 : h ≤ 1 / 10) (hr : Real.sqrt x ≤ r)
    (he : Real.exp (-y) ≤ e)
    (hp :
      (10 / 19 : ℝ) * h * (x * y) + (231 / 2500 : ℝ) * (Real.sqrt (x * y) + 1) / h + 1839 / 1000 ≤
        p)
    (hs : Real.sqrt (x * y) / 20 + (1839 / 1000 : ℝ) * Real.log (x * y) + 21 / 20 ≤ s)
    (hz : Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800 ≤ z)
    (hallow : 0 ≤ p + y * s) (hnum : 0 ≤ x * (1 - e) - e * (p + y * s) - z)
    (hF : F ≤ (x * (1 - e) - e * (p + y * s) - z) / r) :
    F ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hps := add_le_add hp (mul_le_mul_of_nonneg_left hs hy)
  have hp1 := mul_le_mul_of_nonneg_left hps (Real.exp_pos (-y)).le
  have hp2 := mul_le_mul_of_nonneg_right he hallow
  have hp3 := mul_le_mul_of_nonneg_left he (zero_lt_one.trans_le hx).le
  have hn :
    x * (1 - e) - e * (p + y * s) - z ≤
      x * (1 - Real.exp (-y)) -
        Real.exp (-y) *
          (((10 / 19 : ℝ) * h * (x * y) + (231 / 2500 : ℝ) * (Real.sqrt (x * y) + 1) / h +
              1839 / 1000) +
            y * (Real.sqrt (x * y) / 20 + (1839 / 1000 : ℝ) * Real.log (x * y) + 21 / 20)) -
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) := by
    nlinarith only [hp1, hp2, hp3, hz]
  have hd := div_le_div_of_nonneg_left hnum hsx hr
  have hi := div_le_div_of_nonneg_right hn hsx.le
  exact hF.trans (hd.trans (hi.trans (finite_gamma_lower_relative_rh hRH hx hy hcut hh hh1)))

end PseudoPrime.PrimeTestBounds.MillerRabin
