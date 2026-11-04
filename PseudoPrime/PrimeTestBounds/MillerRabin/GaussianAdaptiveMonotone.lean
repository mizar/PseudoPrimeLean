/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianAdaptiveCoefficients

/-! # Monotonicity of the scaled adaptive Gaussian radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above the entrance, the scaled Gaussian slope is monotone. Multiplication by
the scale turns the decreasing correction terms into a square root and a constant,
allowing pointwise witnesses to be transported to a common cumulative scale. -/
theorem adaptiveGaussian_scaled_mono {L M : ℝ} (hL : 2000000000000 ≤ L) (hLM : L ≤ M) :
    adaptiveGaussianA L * L ≤ adaptiveGaussianA M * M := by
  have hl : 0 < L := by linarith only [hL]
  have hm : 0 < M := by linarith only [hL, hLM]
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have he (x : ℝ) (hx : 0 < x) :
    adaptiveGaussianA x * x =
      (2 * (20115621 / 50000000) * x + (61 / 100) * (28794111 / 12500000) * Real.sqrt x + 39) /
        (10971611 / 5000000) := by
    have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
    dsimp only [adaptiveGaussianA]
    field_simp [hx.ne', hp.ne']
    nlinarith only [Real.sq_sqrt hx.le]
  rw [he L hl, he M hm]
  apply (div_le_div_iff_of_pos_right (by norm_num only)).2
  nlinarith only [hLM, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
