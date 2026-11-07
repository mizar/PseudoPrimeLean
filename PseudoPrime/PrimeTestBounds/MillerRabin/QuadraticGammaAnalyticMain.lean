/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaFiniteSigned
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaRelativePsi

/-! # Analytic finite Gamma main sum under RH -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the normalized finite Gamma main sum has an explicit lower
bound for every scale at least one, cutoff above one and relative width in
`(0,1/10]`. Insert the sharp relative Chebyshev bound into the signed-variation
estimate. The result is the analytic main-sum input for the middle cells. -/
theorem finite_gamma_lower_relative_rh (hRH : RiemannHypothesis) {x y h : ℝ} (hx : 1 ≤ x)
    (hy : 0 ≤ y) (hcut : 1 < x * y) (hh : 0 < h) (hh1 : h ≤ 1 / 10) :
    (x * (1 - Real.exp (-y)) -
          Real.exp (-y) *
            (((10 / 19 : ℝ) * h * (x * y) + (231 / 2500 : ℝ) * (Real.sqrt (x * y) + 1) / h +
                1839 / 1000) +
              y * (Real.sqrt (x * y) / 20 + (1839 / 1000 : ℝ) * Real.log (x * y) + 21 / 20)) -
          (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800)) /
        Real.sqrt x ≤
      ∑ n ∈ Finset.Ioc 0 ⌊x * y⌋₊,
        Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n / Real.sqrt x := by
  apply finite_gamma_lower_signed_rh hRH hx hy hcut
  have hpsi := psi_relative_lower hRH hh hh1 (mul_nonneg (zero_lt_one.trans_le hx).le hy)
  linarith only [hpsi]

end PseudoPrime.PrimeTestBounds.MillerRabin
