/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Kernel-checkable lookup in certified prime trees

Binary search in a tree of proved prime labels gives a sound primality test.
Ordering affects completeness and speed but is not needed for soundness.
Balanced trees let finite residue certificates share their primality proofs.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Every nonempty node of a natural-number tree carries a prime.
The empty tree is checked trivially, and a node requires primality of its label and
checked children. This invariant supplies soundness for prime lookup. -/
def primeTreeChecked : BinaryTree ℕ → Prop
  | .nil => True
  | .node p l r => p.Prime ∧ primeTreeChecked l ∧ primeTreeChecked r

/-- Search a natural-number tree by equality and comparison with its root label.
Compare through subtraction from zero to avoid large recursive order tests in the kernel.
Return false at an empty leaf. A positive answer certifies primality when all labels
are prime; no ordering assumption is needed for that implication.
Sorted balanced trees are used to avoid repeated trial division in finite checks. -/
def primeTreeLookup : BinaryTree ℕ → ℕ → Bool
  | .nil, _ => false
  | .node p l r, n =>
    if n - p == 0 then if p - n == 0 then true else primeTreeLookup l n else primeTreeLookup r n

/-- A positive lookup in a checked tree certifies primality of the queried natural.
Induction follows the selected child, or uses the root's prime proof when equality
succeeds. This is the arithmetic justification for a shared Boolean prime cache. -/
theorem primeTreeLookup_prime {t : BinaryTree ℕ} (ht : primeTreeChecked t) {n : ℕ}
    (h : primeTreeLookup t n = true) : n.Prime := by
  induction t with
  | nil => exact Bool.noConfusion h
  | node p l r hl hr =>
    change p.Prime ∧ primeTreeChecked l ∧ primeTreeChecked r at ht
    rw [primeTreeLookup] at h
    split at h
    next hnp =>
      split at h
      next hpn =>
        have hn : n ≤ p := by simpa only [beq_iff_eq, Nat.sub_eq_zero_iff_le] using hnp
        have hp : p ≤ n := by simpa only [beq_iff_eq, Nat.sub_eq_zero_iff_le] using hpn
        exact (Nat.le_antisymm hn hp).symm ▸ ht.1
      next _ => exact hl ht.2.1 h
    next _ => exact hr ht.2.2 h

/-- A list whose labels all pass lookup in a certified tree consists of primes.
Extract each successful Boolean lookup from the list check and use the tree's
shared primality proofs. This verifies supplied witness lists without trial division. -/
theorem primeTreeLookup_all_prime {t : BinaryTree ℕ} {ps : List ℕ} (ht : primeTreeChecked t)
    (h : ps.all (primeTreeLookup t) = true) : ∀ p ∈ ps, p.Prime := by
  intro p hp
  exact primeTreeLookup_prime ht (List.all_eq_true.mp h p hp)

end PseudoPrime.NumberTheory
