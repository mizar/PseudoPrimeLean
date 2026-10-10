/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.FiniteBitMasks
public import Mathlib.Data.List.Sort

/-!
# Relative shifts for finite index masks

Sort the indices and shift only by consecutive gaps, rather than constructing
a separate absolute power of two for every index. The result is the same mask.
This computation supports closed kernel checks with shared certificate data.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Encode ordered indices relative to `base` by shifting across successive gaps.
The head sets the first bit and the tail is encoded relative to that head.
Correct absolute decoding requires ascending indices, all at least `base`;
the sorted mask constructor supplies these conditions. -/
def relativeIndicesMask (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: xs => (1 ||| relativeIndicesMask a xs) <<< (a - base)

/-- Relative encoding of ordered indices at least `base` decodes to the ordinary mask.
Induction composes consecutive shifts, uses the ordering for subtraction cancellation,
and distributes the shift over bitwise union. This justifies the computational shortcut. -/
theorem relativeIndicesMask_shift_eq {xs : List ℕ} (hs : xs.Pairwise (· ≤ ·)) {base : ℕ}
    (hb : ∀ a ∈ xs, base ≤ a) : relativeIndicesMask base xs <<< base = indicesMask xs := by
  induction xs generalizing base with
  | nil => simp only [relativeIndicesMask, indicesMask, Nat.zero_shiftLeft]
  | cons a xs ih =>
    have hc := List.pairwise_cons.mp hs
    have ha := hb a List.mem_cons_self
    rw [relativeIndicesMask, ← Nat.shiftLeft_add, Nat.sub_add_cancel ha, Nat.shiftLeft_or_distrib,
      ih hc.2 hc.1, Nat.shiftLeft_eq, Nat.one_mul, indicesMask]

/-- Permuting an index list preserves its mask.
Compare every bit and use permutation invariance of membership.
This allows the faster mask computation to sort supplied indices. -/
theorem indicesMask_eq_of_perm {xs ys : List ℕ} (h : xs.Perm ys) :
    indicesMask xs = indicesMask ys := by
  apply Nat.eq_of_testBit_eq
  intro a
  exact Bool.eq_iff_iff.mpr (indicesMask_testBit.trans (h.mem_iff.trans indicesMask_testBit.symm))

/-- Encode arbitrary indices after sorting, using shifts across successive gaps.
Merge sort orders the supplied list; duplicates retain the same bit.
The result equals `indicesMask` and avoids repeated absolute powers in closed checks. -/
def sortedIndicesMask (xs : List ℕ) : ℕ :=
  relativeIndicesMask 0 (xs.mergeSort fun a b ↦ decide (a ≤ b))

/-- Sorting and relative shifts compute the same mask as the ordinary index encoding.
Use the sorted-list invariant, decode from base zero and apply permutation invariance.
Consumers can change the kernel computation while retaining the original bit semantics. -/
theorem sortedIndicesMask_eq (xs : List ℕ) : sortedIndicesMask xs = indicesMask xs := by
  have h :=
    relativeIndicesMask_shift_eq (List.pairwise_mergeSort' (· ≤ ·) xs) (fun a _ ↦ Nat.zero_le a)
  rw [Nat.shiftLeft_zero] at h
  exact h.trans (indicesMask_eq_of_perm (List.mergeSort_perm xs _))

end PseudoPrime.NumberTheory
