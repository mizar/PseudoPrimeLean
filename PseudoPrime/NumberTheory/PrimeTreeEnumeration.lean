/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.PrimeLookup
public import PseudoPrime.NumberTheory.FiniteBitMasks

/-!
# Enumeration of certified prime trees

Tree labels can be reused as a prime list without repeating primality checks.
Finite residue coverage masks use this list instead of searching the tree.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Build the residue mask of certified-tree candidates at most `cap` directly.
Prune the right child when the root exceeds the cap, as in capped enumeration.
Combine child masks along the tree instead of constructing and folding a long list.
Completeness is checked separately, so no ordering hypothesis is needed for soundness. -/
def primeTreeResidueMask (q cap : ℕ) : BinaryTree ℕ → ℕ
  | .nil => 0
  | .node p l r =>
    if p - cap == 0 then
      (2 ^ (p % q)) ||| (primeTreeResidueMask q cap l ||| primeTreeResidueMask q cap r)
    else primeTreeResidueMask q cap l

/-- A set bit in a checked prime tree supplies a prime with that residue below the cap.
Induction follows the root bit or a child mask. The root's cap test supplies its bound,
and the tree invariant supplies primality without repeating a primality computation.
This reflects direct tree-mask coverage into bounded prime witnesses. -/
theorem primeTreeResidueMask_exists {t : BinaryTree ℕ} {q cap a : ℕ} (hp : primeTreeChecked t)
    (hb : (primeTreeResidueMask q cap t).testBit a = true) :
    ∃ p : ℕ, p.Prime ∧ p % q = a ∧ p ≤ cap := by
  induction t with
  | nil =>
    exact
      (Bool.false_ne_true (by simpa only [primeTreeResidueMask, Nat.zero_testBit] using hb)).elim
  | node p l r hl hr =>
    change p.Prime ∧ primeTreeChecked l ∧ primeTreeChecked r at hp
    simp only [primeTreeResidueMask] at hb
    split at hb
    next
      hc =>
      rw [Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
        decide_eq_true_eq] at hb
      rcases hb with he | hchild
      · exact ⟨p, hp.1, he, Nat.sub_eq_zero_iff_le.mp (beq_iff_eq.mp hc)⟩
      · rcases hchild with hleft | hright
        · exact hl hp.2.1 hleft
        · exact hr hp.2.2 hright
    next => exact hl hp.2.1 hb

/-- Enumerate all prime-tree labels, visiting the root before its two children.
The list may contain repeated labels. Its membership supplies certified prime
candidates for finite coverage checks when the tree invariant holds. -/
def primeTreeLabels : BinaryTree ℕ → List ℕ
  | .nil => []
  | .node p l r => p :: (primeTreeLabels l ++ primeTreeLabels r)

/-- Every enumerated label of a checked tree is prime.
Induction selects the root or one of the two child lists and uses the corresponding
part of the tree invariant. This reuses the tree's shared primality proofs. -/
theorem primeTreeLabels_prime {t : BinaryTree ℕ} (ht : primeTreeChecked t) {p : ℕ}
    (hp : p ∈ primeTreeLabels t) : p.Prime := by
  induction t with
  | nil => exact (List.not_mem_nil hp).elim
  | node n l r hl
    hr =>
    change
      n.Prime ∧
        PseudoPrime.NumberTheory.primeTreeChecked l ∧
        PseudoPrime.NumberTheory.primeTreeChecked r at ht
    simp only [primeTreeLabels, List.mem_cons, List.mem_append] at hp
    rcases hp with he | hpl | hpr
    · exact he.symm ▸ ht.1
    · exact hl ht.2.1 hpl
    · exact hr ht.2.2 hpr

/-- Enumerate candidate labels at most `cap`, pruning the right child when its root is larger.
For an ordered tree this avoids visiting candidates beyond the bound. Every retained
label comes from the tree; ordering affects completeness, not primality soundness.
This reduces repeated traversal of a shared tree for small finite residue bounds. -/
def primeTreeLabelsAtMost (cap : ℕ) : BinaryTree ℕ → List ℕ
  | .nil => []
  | .node p l r =>
    if p - cap == 0 then p :: (primeTreeLabelsAtMost cap l ++ primeTreeLabelsAtMost cap r)
    else primeTreeLabelsAtMost cap l

/-- All labels retained by the capped enumeration of a certified tree are prime.
Induction selects the root or a retained child label, using the shared prime proofs.
No ordering assumption is required, so closed coverage checks establish completeness. -/
theorem primeTreeLabelsAtMost_prime {t : BinaryTree ℕ} {cap p : ℕ} (ht : primeTreeChecked t)
    (hp : p ∈ primeTreeLabelsAtMost cap t) : p.Prime := by
  induction t with
  | nil => exact (List.not_mem_nil hp).elim
  | node n l r hl hr =>
    change n.Prime ∧ primeTreeChecked l ∧ primeTreeChecked r at ht
    simp only [primeTreeLabelsAtMost] at hp
    split at hp
    next =>
      simp only [List.mem_cons, List.mem_append] at hp
      rcases hp with he | hpl | hpr
      · exact he.symm ▸ ht.1
      · exact hl ht.2.1 hpl
      · exact hr ht.2.2 hpr
    next => exact hl ht.2.1 hp

end PseudoPrime.NumberTheory
