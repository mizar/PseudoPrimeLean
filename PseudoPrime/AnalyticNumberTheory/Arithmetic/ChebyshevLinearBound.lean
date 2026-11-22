/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearConsequences
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiLinearBound.ChebyshevLinearCells

/-! # A global linear Chebyshev bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

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
