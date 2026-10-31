/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaDyadicAnchorBounds

/-! # The intrinsic Gamma Euler cost at anchor 160 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: real p >= 160 and p > 1. Claim: its full Euler cost is at most
(13/25)/(p-1). Reuse the existing dyadic anchor. Role: improve the old positive
coefficient bound without adding numerical data. -/
theorem gamma_euler_anchor160_reciprocal {p : ℝ} (hp : 1 < p) (ha : 160 ≤ p) :
    gammaPrimeEulerCost p ≤ (13 / 25 : ℝ) / (p - 1) := by
  have h :=
    gamma_prime_euler_cost_le_dyadic_anchor (a := 160) (by decide +kernel) hp
      (by
        norm_num only; exact ha)
  norm_num only [gammaDyadicAnchorCap, Rat.cast_div, Rat.cast_ofNat] at h
  exact h

end PseudoPrime.Analysis
