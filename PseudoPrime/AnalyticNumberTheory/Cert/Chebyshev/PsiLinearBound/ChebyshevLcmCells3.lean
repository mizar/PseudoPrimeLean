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

/-- Every integer in [269, 676] belongs to a checked `111/100` cell.
The kernel checks the lcm and linear-budget inequalities at each endpoint. -/
theorem psi_cells_269_676 {n : ℕ} (hlo : 269 ≤ n) (hhi : n ≤ 676) :
    ∃ a b : ℕ, a ≤ n ∧ n ≤ b ∧ Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  by_cases h0 : n ≤ 292
  · refine ⟨269, 292, ?_, h0, ?_⟩
    · exact hlo
    · apply psi_le_111_of_lcm_bound (k := 424)
      · decide +kernel
      · decide +kernel
  · by_cases h1 : n ≤ 316
    · refine ⟨293, 316, ?_, h1, ?_⟩
      · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h0)
      · apply psi_le_111_of_lcm_bound (k := 457)
        · decide +kernel
        · decide +kernel
    · by_cases h2 : n ≤ 352
      · refine ⟨317, 352, ?_, h2, ?_⟩
        · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h1)
        · apply psi_le_111_of_lcm_bound (k := 502)
          · decide +kernel
          · decide +kernel
      · by_cases h3 : n ≤ 388
        · refine ⟨353, 388, ?_, h3, ?_⟩
          · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h2)
          · apply psi_le_111_of_lcm_bound (k := 557)
            · decide +kernel
            · decide +kernel
        · by_cases h4 : n ≤ 430
          · refine ⟨389, 430, ?_, h4, ?_⟩
            · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h3)
            · apply psi_le_111_of_lcm_bound (k := 609)
              · decide +kernel
              · decide +kernel
          · by_cases h5 : n ≤ 466
            · refine ⟨431, 466, ?_, h5, ?_⟩
              · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h4)
              · apply psi_le_111_of_lcm_bound (k := 680)
                · decide +kernel
                · decide +kernel
            · by_cases h6 : n ≤ 508
              · refine ⟨467, 508, ?_, h6, ?_⟩
                · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h5)
                · apply psi_le_111_of_lcm_bound (k := 733)
                  · decide +kernel
                  · decide +kernel
              · by_cases h7 : n ≤ 568
                · refine ⟨509, 568, ?_, h7, ?_⟩
                  · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h6)
                  · apply psi_le_111_of_lcm_bound (k := 802)
                    · decide +kernel
                    · decide +kernel
                · by_cases h8 : n ≤ 618
                  · refine ⟨569, 618, ?_, h8, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h7)
                    · apply psi_le_111_of_lcm_bound (k := 894)
                      · decide +kernel
                      · decide +kernel
                  · refine ⟨619, 676, ?_, hhi, ?_⟩
                    · exact Nat.succ_le_of_lt (Nat.lt_of_not_ge h8)
                    · apply psi_le_111_of_lcm_bound (k := 981)
                      · decide +kernel
                      · decide +kernel

end PseudoPrime.AnalyticNumberTheory.Arithmetic
