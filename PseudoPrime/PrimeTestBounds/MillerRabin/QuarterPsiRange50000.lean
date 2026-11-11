/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiEntrance
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCell1
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCell2
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCell3
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiCell4

/-! # Chebyshev lower bound through the finite row cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The certified interval bounds imply `x - 600 ≤ psi x` from 39760 to 50000. -/
theorem psi_lower_39760_50000 {x : ℝ} (ha : 39760 ≤ x) (hb : x < 50000) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h40000 : x < 40000
  · exact psi_lower_entrance ha h40000
  by_cases h42560 : x < 42560
  · exact psi_lower_40000_42560 (le_of_not_gt h40000) h42560
  by_cases h45120 : x < 45120
  · exact psi_lower_42560_45120 (le_of_not_gt h42560) h45120
  by_cases h47680 : x < 47680
  · exact psi_lower_45120_47680 (le_of_not_gt h45120) h47680
  · exact psi_lower_47680_50000 (le_of_not_gt h47680) hb

end PseudoPrime.PrimeTestBounds.MillerRabin
