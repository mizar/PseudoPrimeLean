/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleGap
public import PseudoPrime.LLS.GammaEulerTailErrorCertificate

/-! # Transfer of finite numerical bounds to the coupled Gamma gap -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, a center upper bound at 50000 implies total Euler mass at most
3093/250. Retain the certified infinite-tail error of 1/2500. This isolates
the finite center certificate required by the middle-cell proof. -/
theorem euler_mass_le_12372_of_center (hRH : RiemannHypothesis)
    (hc : LLS.gammaEulerMassCenter 50000 ≤ (30929 / 2500 : ℝ)) :
    (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) ≤ (3093 / 250 : ℝ) := by
  have h := (LLS.gammaEulerMass_bounds_50000 hRH).2
  linarith only [h, hc]

/-- Certified finite-prefix lower bounds, a principal-series upper bound
and total Euler mass 3093/250 transfer a strict numerical margin to the
actual Gamma gap. Monotonicity of the four scalar inputs proves the
comparison. This connects interval certificates to the witness criterion. -/
theorem gamma_gap_of_numeric_bounds (s : Finset ℕ) (x L S U P : ℝ)
    (hS : S ≤ ∑ k ∈ s, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x)
    (hU : (∑' k : ℕ, Real.exp (-(k : ℝ) / x) * ArithmeticFunction.vonMangoldt k / Real.sqrt x) ≤ U)
    (hP : P ≤ ∑ k ∈ s, Analysis.gammaResolventMangoldtWeight k)
    (hE : (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) ≤ (3093 / 250 : ℝ))
    (hnum :
      U + 2 * (11783423 / 25000000 : ℝ) * L - 477 / 100 + (3093 / 250 - 4 * P) +
          ((7 / 3 : ℝ) * L + 12) / Real.sqrt x +
          (105 / 2 : ℝ) * x ^ (-9 / 16 : ℝ) +
          3 / (x * Real.sqrt x) <
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
  linarith only [hS, hU, hP, hE, hnum]

end PseudoPrime.PrimeTestBounds.MillerRabin
