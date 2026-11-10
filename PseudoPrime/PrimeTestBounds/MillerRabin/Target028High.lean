/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePiecewise
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedRootComparison

/-! # Three-tenths root refinement on the high logarithmic range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For logarithmic scale at least 2000, the square root of the linear
comparison cutoff is at most `17/1000` times the scale. Squaring the
positive sides reduces the comparison to a rational quadratic inequality. -/
theorem target028_sqrt_cap {L : ℝ} (hL : 2000 ≤ L) :
    Real.sqrt ((5291 / 10000 : ℝ) * L) ≤ (17 / 1000 : ℝ) * L := by
  apply (Real.sqrt_le_left (show (0 : ℝ) ≤ (17 / 1000 : ℝ) * L by linarith only [hL])).mpr
  nlinarith only [hL, sq_nonneg (L - 2000)]

/-- The quadratic defining the paper root is nonpositive at a comparison
radius with the stated square and linear upper bound. The rational margin
holds uniformly for every allowance at most three. -/
theorem target028_root_budget {L K z : ℝ} (hL : 2000 ≤ L) (hK3 : K ≤ 3)
    (hzsq : z ^ 2 = (5291 / 10000 : ℝ) * L) (hzcap : z ≤ (17 / 1000 : ℝ) * L) :
    (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * z ≤ (24439 / 50000 : ℝ) * z ^ 2 := by
  norm_num only at ⊢
  nlinarith only [hzsq, hzcap, hL, hK3]

/-- For logarithmic scale at least 2000 and allowance between zero and three,
the squared paper root is bounded by `5291/10000` times the scale. This
explicit comparison will bound the high-range fourth-power cutoff. -/
theorem target028_root_sq_le {L K : ℝ} (hL : 2000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperRoot L K ^ 2 ≤ (5291 / 10000 : ℝ) * L := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  let z : ℝ := Real.sqrt ((5291 / 10000 : ℝ) * L)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hzsq : z ^ 2 = (5291 / 10000 : ℝ) * L := Real.sq_sqrt (mul_nonneg (by norm_num only) hL0)
  have hz20 : (20 : ℝ) ≤ z := by nlinarith only [hzsq, hz0, hL]
  have hbudget := target028_root_budget hL hK3 hzsq (target028_sqrt_cap hL)
  have hs := refined_root_le_of_budget hL0 hK hz20 hbudget
  have hp := refined_paper_root_positive L K
  have hsq := pow_le_pow_left₀ hp.le hs 2
  simpa only [hzsq] using hsq

/-- For every scale at least 2000 and allowance between zero and three, the
paper's fourth-power cutoff is at most `7/25` times the squared logarithmic
scale. Squaring the root bound supplies the numerical comparison. -/
theorem target028_bound_le {L K : ℝ} (hL : 2000 ≤ L) (hK : 0 ≤ K) (hK3 : K ≤ 3) :
    refinedPaperBound L K ≤ (7 / 25 : ℝ) * L ^ 2 := by
  have hroot := target028_root_sq_le hL hK hK3
  have hsq := pow_le_pow_left₀ (sq_nonneg (refinedPaperRoot L K)) hroot 2
  dsimp only [refinedPaperBound]
  nlinarith only [hsq, sq_nonneg L]

/-- The selected piecewise cutoff is at most `7/25` times the squared
logarithmic scale from 2000 onward. Its selected allowance is between zero
and three, so the uniform cutoff comparison applies on every branch. -/
theorem target028_piecewise_le {L : ℝ} (hL : 2000 ≤ L) :
    refinedPaperCoefficient L * L ^ 2 ≤ (7 / 25 : ℝ) * L ^ 2 := by
  rw [refined_piecewise_high (by linarith only [hL] : (1000 : ℝ) ≤ L)]
  exact target028_bound_le hL (refined_allowance_range L).1 (refined_allowance_range L).2

end PseudoPrime.PrimeTestBounds.MillerRabin
