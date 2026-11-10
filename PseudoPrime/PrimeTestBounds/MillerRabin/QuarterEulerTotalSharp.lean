/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerLowerClosed
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerEndpointBounds

/-! Sharp lower bound for the refined Euler total under RH. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the refined Euler total exceeds 843/400 times the kernel normalization. Combine
the checked prefix, endpoint corrections and tail estimates. This sharp mass bound is used in
the quarter-coefficient uniform Miller–Rabin estimate. -/
theorem quarter_euler_total_lower_sharp (hRH : RiemannHypothesis) :
    (843 / 400 : ℝ) * (27 / 25 : ℝ) ^ 5 <
      ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * refinedSixEulerWeight n := by
  have h := quarter_euler_lower_1000_tails hRH
  have hb := quarter_euler_boundary_lower
  norm_num only at h hb ⊢
  linarith only [h, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
