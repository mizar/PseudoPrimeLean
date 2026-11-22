/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLcmCertificates

/-! # Finite integer certificates for a linear Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Every integer in [1, 26] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_1_26 {n : ℕ} (hlo : 1 ≤ n) (hhi : n ≤ 26) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 2
  · refine ⟨1, 2, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 1)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 4
    · refine ⟨3, 4, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 4)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 6
      · refine ⟨5, 6, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 6)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 8
        · refine ⟨7, 8, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 10)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 10
          · refine ⟨9, 10, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 12)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 12
            · refine ⟨11, 12, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 15)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 16
              · refine ⟨13, 16, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 20)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 18
                · refine ⟨17, 18, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 24)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 22
                  · refine ⟨19, 22, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 28)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨23, 26, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 35)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
