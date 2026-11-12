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

/-- Every integer in [4567, 11723] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_4567_11723 {n : ℕ} (hlo : 4567 ≤ n) (hhi : n ≤ 11723) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 5010
  · refine ⟨4567, 5010, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 7236)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 5506
    · refine ⟨5011, 5506, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 7940)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 6066
      · refine ⟨5507, 6066, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 8727)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 6678
        · refine ⟨6067, 6678, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 9620)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 7348
          · refine ⟨6679, 7348, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 10588)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 8092
            · refine ⟨7349, 8092, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 11653)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 8892
              · refine ⟨8093, 8892, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 12829)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 9748
                · refine ⟨8893, 9748, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 14089)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 10690
                  · refine ⟨9749, 10690, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 15447)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨10691, 11723, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 16853)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
