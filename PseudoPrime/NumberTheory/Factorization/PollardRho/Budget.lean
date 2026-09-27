/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Basic

/-!
# Whole-tree Pollard rho budgets
-/

namespace PseudoPrime.NumberTheory.Factorization.PollardRho

/-- An explicit binary budget tree assigns a separate rho allowance to every possible split.
Leaves stop unresolved; internal nodes spend their own allowance once and pass the two subtrees to
the resulting factors. This gives a genuine whole-tree work cap rather than reusing one fuel at
every recursive node. -/
inductive RhoBudgetTree where
  | leaf : RhoBudgetTree
  | split (fuel : ℕ) (left right : RhoBudgetTree) : RhoBudgetTree
  deriving DecidableEq, Repr

/-- Sum of the local rho allowances assigned to every internal node of the budget tree. -/
def RhoBudgetTree.totalFuel : RhoBudgetTree → ℕ
  | .leaf => 0
  | .split fuel left right => fuel + left.totalFuel + right.totalFuel

/-- Split one integer round allowance evenly among a node and its two child subtrees.
The requested depth bounds the number of split levels; small budgets naturally assign zero fuel
to deeper nodes. -/
def balancedRhoBudgetTree : ℕ → ℕ → RhoBudgetTree
  | 0, _ => .leaf
  | depth + 1, budget =>
    let childBudget := budget / 3
    .split childBudget (balancedRhoBudgetTree depth childBudget)
      (balancedRhoBudgetTree depth childBudget)

/-- The balanced allocator never assigns more aggregate Floyd-round fuel than the input budget. -/
theorem balancedRhoBudgetTree_totalFuel_le (depth budget : ℕ) :
    (balancedRhoBudgetTree depth budget).totalFuel ≤ budget := by
  induction depth generalizing budget with
  | zero =>
    exact Nat.zero_le budget
  | succ depth ih =>
    let childBudget := budget / 3
    have hleft := ih childBudget
    simp only [balancedRhoBudgetTree, RhoBudgetTree.totalFuel]
    calc
        childBudget +
          (balancedRhoBudgetTree depth childBudget).totalFuel +
            (balancedRhoBudgetTree depth childBudget).totalFuel ≤
        childBudget + childBudget + childBudget := by
          exact Nat.add_le_add (Nat.add_le_add_left hleft childBudget) hleft
      _ ≤ budget := by
        have hdiv := Nat.div_mul_le_self budget 3
        dsimp only [childBudget]
        simpa only [Nat.mul_succ, Nat.mul_zero, Nat.zero_add] using hdiv

end PseudoPrime.NumberTheory.Factorization.PollardRho
