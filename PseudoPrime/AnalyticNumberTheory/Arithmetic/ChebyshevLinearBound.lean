/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearConsequences
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells0
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells1
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells2
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells3
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells4
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells5
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmCells6

/-! # A global linear Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

private theorem psi_111_cells (n : ℕ) (hlo : 1 ≤ n) (hhi : n ≤ 11723) :
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

/-- For every nonnegative real argument, `psi x ≤ 111x/100` without RH.
Integer endpoint certificates cover the finite prefix; the five-term estimate
extends the result to all larger arguments by strong induction. -/
theorem psi_le_111 {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ (111 / 100 : ℝ) * x := by
  exact psi_le_111_of_nat_cells psi_111_cells x hx

/-- For `x ≥ 1`, the higher prime-power contribution is at most `111 sqrt x / 50`.
Combine the global linear psi bound with the Costa-Pereira three-root estimate. -/
theorem psi_sub_theta_le_111_fifty_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ (111 / 50 : ℝ) * Real.sqrt x := by
  apply psi_sub_theta_le_111_fifty_of_prefix hx
  intro t ht _
  exact psi_le_111 ht

/-- For `x ≥ 1`, weights bounded above by `1/3` give a doubled nonprime Mangoldt
mass at most `37 sqrt x / 25`. This uses the unconditional linear psi bound. -/
theorem composite_weight_le_37_25_sqrt {x : ℝ} (hx : 1 ≤ x) (w : ℕ → ℝ)
    (hw : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊, w n ≤ 1 / 3) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime),
        2 * ArithmeticFunction.vonMangoldt n * w n) ≤
      (37 / 25 : ℝ) * Real.sqrt x := by
  apply composite_weight_le_37_25_of_prefix hx w hw
  intro t ht _
  exact psi_le_111 ht

end PseudoPrime.AnalyticNumberTheory.Arithmetic
