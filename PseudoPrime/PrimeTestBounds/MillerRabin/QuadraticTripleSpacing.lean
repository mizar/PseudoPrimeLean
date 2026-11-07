/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Real.Sqrt

/-! # Real spacing bound for uniform Korselt triples -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the positive gaps satisfy the divisibility-derived inequality
`2a ≤ d(f+1)`, then `d+2f ≥ 4√a-2`. The square of the difference between
`f+1` and `√a` supplies the arithmetic-geometric comparison. This is the
real spacing estimate used in the low-range local-modulus improvement. -/
theorem weighted_spacing_lower {a d f : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) (hf : 0 ≤ f + 1)
    (hgap : 2 * a ≤ d * (f + 1)) : 4 * Real.sqrt a - 2 ≤ d + 2 * f := by
  have hs := Real.sq_sqrt ha
  have hsq := sq_nonneg (f + 1 - Real.sqrt a)
  by_cases hz : f + 1 = 0
  · rw [hz, mul_zero] at hgap
    have ha0 : a = 0 := by linarith only [hgap, ha]
    rw [ha0, Real.sqrt_zero]
    linarith only [hd, hz]
  · have hfpos : 0 < f + 1 := lt_of_le_of_ne hf (Ne.symm hz)
    by_contra h
    have hneg : d + 2 * f < 4 * Real.sqrt a - 2 := lt_of_not_ge h
    have hm := mul_pos (sub_pos.mpr hneg) hfpos
    nlinarith only [hs, hsq, hgap, hm]

/-- For ordered real factors `p ≤ q ≤ q+f`, the divisibility-derived gap
inequality yields a lower bound for the squared largest factor. Monotonicity
of square root replaces `q` by `p`, while the remaining square is nonnegative.
This is the numerator estimate used to bound the local pair modulus. -/
theorem triple_spacing_square {p q f : ℝ} (hp : 1 ≤ p) (hpq : p ≤ q) (hf : 0 ≤ f)
    (hgap : 2 * (q - 1) ≤ (q - p) * (f + 1)) :
    p * q + q * (4 * Real.sqrt (p - 1) - 2) ≤ (q + f) ^ 2 := by
  have ha : 0 ≤ q - 1 := by linarith only [hp, hpq]
  have hd : 0 ≤ q - p := sub_nonneg.mpr hpq
  have hf1 : 0 ≤ f + 1 := by linarith only [hf]
  have hw := weighted_spacing_lower ha hd hf1 hgap
  have hr := Real.sqrt_le_sqrt (sub_le_sub_right hpq 1)
  have hq : 0 ≤ q := by linarith only [hp, hpq]
  have hm :=
    mul_nonneg hq (show 0 ≤ (q - p) + 2 * f - (4 * Real.sqrt (p - 1) - 2) by linarith only [hw, hr])
  nlinarith only [hm, sq_nonneg f]

end PseudoPrime.PrimeTestBounds.MillerRabin
