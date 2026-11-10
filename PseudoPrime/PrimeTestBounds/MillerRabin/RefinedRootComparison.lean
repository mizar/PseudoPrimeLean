/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePaperRoot

/-! # Comparison with the refined paper root -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A comparison radius at least 20 satisfying the quadratic budget bounds
the positive paper root. Compare the root equation with the budget and use
positivity of the factored difference. -/
theorem refined_root_le_of_budget {L K z : ℝ} (hL : 0 ≤ L) (hK : 0 ≤ K) (hz : 20 ≤ z)
    (hbudget :
      (3 / (8 * (27 / 25 : ℝ) ^ 5)) * L + K + (53 / 500 : ℝ) * z ≤ (24439 / 50000 : ℝ) * z ^ 2) :
    refinedPaperRoot L K ≤ z := by
  have he := refined_paper_root_equation hL hK
  have hp := refined_paper_root_positive L K
  by_contra hn
  have hd : 0 < refinedPaperRoot L K - z := sub_pos.mpr (lt_of_not_ge hn)
  have hm :=
    mul_pos hd
      (show 0 < (24439 / 50000 : ℝ) * (refinedPaperRoot L K + z) - 53 / 500 by
        nlinarith only [hp, hz])
  norm_num only at he hbudget hm
  nlinarith only [he, hbudget, hm]

end PseudoPrime.PrimeTestBounds.MillerRabin
