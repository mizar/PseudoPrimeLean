/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Bitwise

/-!
# Finite index sets represented by natural-number bit masks

Membership is a bit test, and inclusion is checked by bitwise intersection.
These identities support kernel-checked finite coverage certificates.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Pack the values of `f` on `start, ..., start + count - 1` into successive bits.
Bit zero corresponds to `start`. Building with `Nat.bit` avoids repeated unions
with large powers of two when a dense interval of predicate values is encoded. -/
def predicateMask (f : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, count + 1 => Nat.bit (f start) (predicateMask f (start + 1) count)

/-- For an index below `count`, the corresponding packed bit is `f (start + a)`.
Induction removes the least significant bit and advances the starting index.
This identifies required residue bits without constructing an intermediate list. -/
theorem predicateMask_testBit (f : ℕ → Bool) {start count a : ℕ} (ha : a < count) :
    (predicateMask f start count).testBit a = f (start + a) := by
  induction count generalizing start a with
  | zero => exact (Nat.not_lt_zero a ha).elim
  | succ count ih =>
    cases a with
    | zero => simp only [predicateMask, Nat.testBit_bit_zero, Nat.add_zero]
    | succ a =>
      rw [predicateMask, Nat.testBit_bit_succ, ih (Nat.lt_of_succ_lt_succ ha)]
      simp only [Nat.add_assoc, Nat.add_comm 1 a]

/-- Encode a list of natural indices by setting the corresponding bits. -/
def indicesMask : List ℕ → ℕ
  | [] => 0
  | a :: l => (2 ^ a) ||| indicesMask l

/-- A bit is set precisely when its index occurs in the encoded list.
Induction uses the bitwise union and the single-bit power of two. -/
theorem indicesMask_testBit {l : List ℕ} {a : ℕ} : (indicesMask l).testBit a = true ↔ a ∈ l := by
  induction l with
  | nil => simp only [indicesMask, Nat.zero_testBit, Bool.false_eq_true, List.not_mem_nil]
  | cons b l
    ih =>
    rw [indicesMask, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow, ih]
    simp only [decide_eq_true_eq, List.mem_cons]
    exact or_congr eq_comm Iff.rfl

/-- The mask of concatenated index lists is the union of their separate masks.
Induction and associativity of bitwise union justify checking short lists separately
and combining their masks without reevaluating a long recursive list. -/
theorem indicesMask_append (xs ys : List ℕ) :
    indicesMask (xs ++ ys) = indicesMask xs ||| indicesMask ys := by
  induction xs with
  | nil => exact (Nat.zero_or (indicesMask ys)).symm
  | cons a xs ih => simp only [List.cons_append, indicesMask, ih, Nat.lor_assoc]

/-- Check bit-set inclusion by intersection with the required mask. -/
def maskIncludes (covered required : ℕ) : Bool :=
  (covered &&& required) == required

/-- Successful inclusion transfers any required bit into the covering mask.
Apply the bit projection to the checked equality and use the intersection formula. -/
theorem maskIncludes_testBit {covered required a : ℕ} (h : maskIncludes covered required = true)
    (ha : required.testBit a = true) : covered.testBit a = true := by
  have he : covered &&& required = required := beq_iff_eq.mp h
  have hb := congrArg (fun n : ℕ ↦ n.testBit a) he
  simpa only [Nat.testBit_land, ha, Bool.and_true] using hb

end PseudoPrime.NumberTheory
