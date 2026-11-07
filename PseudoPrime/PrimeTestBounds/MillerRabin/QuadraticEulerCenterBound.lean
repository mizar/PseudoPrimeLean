/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerCenterScalars
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPsiBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaCellTransfer

/-! # Closed finite-center certificate for the coupled Gamma comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH the actual Euler mass center at 50000 is at most 12.3716.
Combine the checked Euler prefix, exact-support Chebyshev lower certificate,
signed scalar bounds and existing smoothed arithmetic lower bound.
All finite numerical inputs are discharged by kernel certificates. -/
theorem center50000_upper (hRH : RiemannHypothesis) :
    LLS.gammaEulerMassCenter 50000 ≤ (30929 / 2500 : ℝ) := by
  have hU :
    (∑ m ∈ Finset.Ioc 0 ⌊(50000 : ℝ)⌋₊, Analysis.gammaResolventMangoldtWeight m) ≤
      (5805279 / 1000000 : ℝ) := by
    simpa only [Nat.floor_ofNat] using center50000_prefix_upper
  have hc :=
    LLS.gamma_center_le_of_interval_inputs hU center50000_weight_lower
      (by norm_num only : (0 : ℝ) ≤ 6716713 / 1000000000000) center50000_psi_lower
      (by norm_num only : (0 : ℝ) ≤ 999719 / 20) center50000_slope_upper
      (by norm_num only : (-(88831 / 12500000000) : ℝ) ≤ 0) (LLS.gamma_smoothed_cutoff_lower hRH)
      (by norm_num only : (0 : ℝ) ≤ 49965) center50000_main_upper
  have hn :
    (5805279 / 1000000 : ℝ) - (6716713 / 1000000000000) * (999719 / 20) +
        (-(88831 / 12500000000)) * 49965 +
        58051 / 8000 ≤
      30929 / 2500 := by
    norm_num only
  exact hc.trans hn

/-- Under RH the actual infinite Gamma Euler mass is at most 12.372.
Add the certified infinite-tail error to the fully certified finite center.
This removes the numerical Euler-mass premise from the middle-cell route. -/
theorem euler_mass_le_12372 (hRH : RiemannHypothesis) :
    (∑' k : ℕ, Analysis.gammaResolventMangoldtWeight k) ≤ (3093 / 250 : ℝ) :=
  euler_mass_le_12372_of_center hRH (center50000_upper hRH)

end PseudoPrime.PrimeTestBounds.MillerRabin
