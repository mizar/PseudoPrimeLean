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

/-- Every integer in [27, 100] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_27_100 {n : ℕ} (hlo : 27 ≤ n) (hhi : n ≤ 100) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 30
  · refine ⟨27, 30, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 42)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 36
    · refine ⟨31, 36, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 48)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 42
      · refine ⟨37, 42, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 58)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 46
        · refine ⟨43, 46, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 64)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 52
          · refine ⟨47, 52, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 72)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 60
            · refine ⟨53, 60, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 84)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 70
              · refine ⟨61, 70, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 96)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 78
                · refine ⟨71, 78, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 109)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 88
                  · refine ⟨79, 88, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 123)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨89, 100, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 136)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
