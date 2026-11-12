/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCertificates

/-! # Finite integer certificates for a linear Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Every integer in [101, 268] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_101_268 {n : ℕ} (hlo : 101 ≤ n) (hhi : n ≤ 268) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 108
  · refine ⟨101, 108, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 156)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 120
    · refine ⟨109, 120, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 170)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 136
      · refine ⟨121, 136, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 191)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 150
        · refine ⟨137, 150, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 212)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 166
          · refine ⟨151, 166, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 234)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 180
            · refine ⟨167, 180, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 260)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 196
              · refine ⟨181, 196, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 283)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 222
                · refine ⟨197, 222, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 306)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 242
                  · refine ⟨223, 242, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 353)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨243, 268, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 379)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
