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

/-- Every integer in [1753, 4566] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_1753_4566 {n : ℕ} (hlo : 1753 ≤ n) (hhi : n ≤ 4566) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 1932
  · refine ⟨1753, 1932, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 2779)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 2128
    · refine ⟨1933, 2128, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 3055)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 2340
      · refine ⟨2129, 2340, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 3366)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 2590
        · refine ⟨2341, 2590, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 3707)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 2832
          · refine ⟨2591, 2832, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 4100)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 3120
            · refine ⟨2833, 3120, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 4492)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 3456
              · refine ⟨3121, 3456, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 4938)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 3792
                · refine ⟨3457, 3792, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 5470)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 4156
                  · refine ⟨3793, 4156, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 6009)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨4157, 4566, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 6583)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
