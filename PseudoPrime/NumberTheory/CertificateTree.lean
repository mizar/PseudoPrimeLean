/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Bool.Basic
public import Mathlib.Data.Tree.Basic

/-!
# Checked certificate trees with natural-number keys

Balanced trees share certificate data and checks without a proof branch for every key.
Lookup soundness identifies the key and recovers its successful Boolean check.
Ordering is needed for efficient complete lookup, but not for this soundness statement.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Search for a natural-number key by comparing it with the current node's key.
Return its certificate on equality, or visit the selected child otherwise.
Balanced ordered data give shallow lookup; soundness does not assume ordering. -/
def certificateTreeLookup {α : Type*} (key : α → ℕ) : BinaryTree α → ℕ → Option α
  | .nil, _ => none
  | .node a l r, q =>
    if q - key a == 0 then if key a - q == 0 then some a else certificateTreeLookup key l q
    else certificateTreeLookup key r q

/-- Require a proposition at every label of a certificate tree.
Nodes combine independently established certificates without evaluating a Boolean
conjunction of all their checks. This shares expensive closed numerical proofs. -/
def certificateTreeForall {α : Type*} (P : α → Prop) : BinaryTree α → Prop
  | .nil => True
  | .node a l r => P a ∧ certificateTreeForall P l ∧ certificateTreeForall P r

/-- Lookup in a certified tree returns the queried key and the label's proposition.
Follow the lookup's selected branch; equality identifies the key and supplies the
root certificate. Ordering is unnecessary for this soundness implication. -/
theorem certificateTreeForall_lookup {α : Type*} {key : α → ℕ} {P : α → Prop} {t : BinaryTree α}
    {q : ℕ} {a : α} (ht : certificateTreeForall P t) (h : certificateTreeLookup key t q = some a) :
    key a = q ∧ P a := by
  induction t with
  | nil => exact (Option.some_ne_none a h.symm).elim
  | node b l r hl hr =>
    rw [certificateTreeLookup] at h
    split at h
    next hqb =>
      split at h
      next hbq =>
        have hq : q ≤ key b := Nat.sub_eq_zero_iff_le.mp (beq_iff_eq.mp hqb)
        have hb : key b ≤ q := Nat.sub_eq_zero_iff_le.mp (beq_iff_eq.mp hbq)
        have he := Option.some.inj h
        exact ⟨(congrArg key he).symm.trans (Nat.le_antisymm hb hq), he ▸ ht.1⟩
      next _ => exact hl ht.2.1 h
    next _ => exact hr ht.2.2 h

/-- Check every certificate in a tree with the supplied Boolean predicate.
An empty tree passes, and a node requires its own check and both child checks.
Named small subtrees allow closed checks to be shared by their lookup consumers. -/
def certificateTreeAllCheck {α : Type*} (check : α → Bool) : BinaryTree α → Bool
  | .nil => true
  | .node a l r => check a && (certificateTreeAllCheck check l && certificateTreeAllCheck check r)

/-- Lookup in a successfully checked tree returns the queried key and a passing certificate.
Induction follows the selected child; the equality branch reflects both subtraction
tests and reads the root check. This connects shared finite checks to arbitrary queries. -/
theorem certificateTreeAllCheck_lookup {α : Type*} {key : α → ℕ} {check : α → Bool}
    {t : BinaryTree α} {q : ℕ} {a : α} (ht : certificateTreeAllCheck check t = true)
    (h : certificateTreeLookup key t q = some a) : key a = q ∧ check a = true := by
  induction t with
  | nil => exact (Option.some_ne_none a h.symm).elim
  | node b l r hl hr =>
    have hc := Bool.and_eq_true_iff.mp ht
    rw [certificateTreeLookup] at h
    split at h
    next hqb =>
      split at h
      next hbq =>
        have hq : q ≤ key b := Nat.sub_eq_zero_iff_le.mp (beq_iff_eq.mp hqb)
        have hb : key b ≤ q := Nat.sub_eq_zero_iff_le.mp (beq_iff_eq.mp hbq)
        have he := Option.some.inj h
        exact ⟨(congrArg key he).symm.trans (Nat.le_antisymm hb hq), he ▸ hc.1⟩
      next _ => exact hl (Bool.and_eq_true_iff.mp hc.2).1 h
    next _ => exact hr (Bool.and_eq_true_iff.mp hc.2).2 h

/-- A passing root certificate and two checked child trees give a checked node.
Combine their Boolean conjunctions without evaluating the checks again.
This shares independent finite checks when assembling large certificate trees. -/
theorem certificateTreeAllCheck_node {α : Type*} {check : α → Bool} {a : α} {l r : BinaryTree α}
    (ha : check a = true) (hl : certificateTreeAllCheck check l = true)
    (hr : certificateTreeAllCheck check r = true) :
    certificateTreeAllCheck check (.node a l r) = true := by
  exact Bool.and_eq_true_iff.mpr ⟨ha, Bool.and_eq_true_iff.mpr ⟨hl, hr⟩⟩

/-- A successful Boolean tree check yields the corresponding propositions after
mapping each entry. Assume each passing check implies the mapped predicate.
Induction reads the root and child checks without reevaluating their arithmetic.
This separates numerical certificate data from the lookup tree used by consumers. -/
theorem certificateTreeForall_map_of_allCheck {α β : Type*} (f : α → β) (check : α → Bool)
    (P : β → Prop) (hs : ∀ a, check a = true → P (f a)) {t : BinaryTree α}
    (ht : certificateTreeAllCheck check t = true) : certificateTreeForall P (t.map f) := by
  induction t with
  | nil => exact True.intro
  | node a l r hl
    hr =>
    rw [certificateTreeAllCheck, Bool.and_eq_true, Bool.and_eq_true] at ht
    exact ⟨hs a ht.1, hl ht.2.1, hr ht.2.2⟩

end PseudoPrime.NumberTheory
