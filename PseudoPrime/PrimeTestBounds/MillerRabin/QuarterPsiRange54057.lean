/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiRange50000
import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticEulerPsiBound
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh1
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh2
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh3
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh4
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh5
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh6
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiHigh7

/-! # Finite Chebyshev lower bound for uniform quarter witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `39760 ≤ x < 54057`, certified finite intervals imply `x - 600 ≤ psi x`.
The proof combines the independently verified prefix and prime-count intervals. -/
theorem psi_lower_39760_54057 {x : ℝ} (ha : 39760 ≤ x) (hb : x < 54057) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h50000 : x < 50000
  · exact psi_lower_39760_50000 ha h50000
  by_cases h50512 : x < 50512
  · have ha' : (50000 : ℝ) ≤ x := le_of_not_gt h50000
    have hm := Chebyshev.psi_mono ha'
    have hbase := center50000_psi_lower
    linarith only [hm, hbase, h50512]
  by_cases h51024 : x < 51024
  · exact psi_lower_50512_51024 (le_of_not_gt h50512) h51024
  by_cases h51536 : x < 51536
  · exact psi_lower_51024_51536 (le_of_not_gt h51024) h51536
  by_cases h52048 : x < 52048
  · exact psi_lower_51536_52048 (le_of_not_gt h51536) h52048
  by_cases h52560 : x < 52560
  · exact psi_lower_52048_52560 (le_of_not_gt h52048) h52560
  by_cases h53072 : x < 53072
  · exact psi_lower_52560_53072 (le_of_not_gt h52560) h53072
  by_cases h53584 : x < 53584
  · exact psi_lower_53072_53584 (le_of_not_gt h53072) h53584
  · exact psi_lower_53584_54057 (le_of_not_gt h53584) hb

end PseudoPrime.PrimeTestBounds.MillerRabin
