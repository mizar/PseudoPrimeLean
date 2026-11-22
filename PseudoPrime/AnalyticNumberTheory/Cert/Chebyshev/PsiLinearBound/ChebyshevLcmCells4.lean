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

/-- Every integer in [677, 1752] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_677_1752 {n : ℕ} (hlo : 677 ≤ n) (hhi : n ≤ 1752) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 742
  · refine ⟨677, 742, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 1068)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 822
    · refine ⟨743, 822, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 1173)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 910
      · refine ⟨823, 910, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 1305)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 1008
        · refine ⟨911, 1008, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 1438)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 1096
          · refine ⟨1009, 1096, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 1590)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 1212
            · refine ⟨1097, 1212, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 1732)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 1320
              · refine ⟨1213, 1320, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 1918)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 1458
                · refine ⟨1321, 1458, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 2094)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 1600
                  · refine ⟨1459, 1600, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 2305)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨1601, 1752, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 2535)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
