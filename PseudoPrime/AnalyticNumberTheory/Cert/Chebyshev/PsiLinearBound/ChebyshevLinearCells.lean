/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells0
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells1
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells2
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells3
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells4
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells5
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCells6

/-! # Combining certified linear psi cells -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The finite endpoint certificates provide the linear-bound cell covering each integer up to
11723. The resulting proposition is used to extend the estimate to all real inputs. -/
theorem psi_111_cells (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 11723) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 26
  · exact psi_cells_1_26 hlo h0
  · have hl1 : 27 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
    by_cases h1 : n ≤ 100
    · exact psi_cells_27_100 hl1 h1
    · have hl2 : 101 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
      by_cases h2 : n ≤ 268
      · exact psi_cells_101_268 hl2 h2
      · have hl3 : 269 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
        by_cases h3 : n ≤ 676
        · exact psi_cells_269_676 hl3 h3
        · have hl4 : 677 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
          by_cases h4 : n ≤ 1752
          · exact psi_cells_677_1752 hl4 h4
          · have hl5 : 1753 ≤ n := Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
            by_cases h5 : n ≤ 4566
            · exact psi_cells_1753_4566 hl5 h5
            · exact psi_cells_4567_11723 (Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)) hhi

end PseudoPrime.AnalyticNumberTheory.Arithmetic
