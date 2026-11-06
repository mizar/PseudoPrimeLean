/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCount

/-! # Kernel-checkable tables for weighted multiset counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Check the positive weight, row lengths and every unbounded-knapsack
update through budget `N`. Entries outside the arrays use zero, but the size
checks ensure that every checked index belongs to both rows. -/
def weightedPrimeRowCheck (p N : ℕ) (old new : Array ℕ) : Bool :=
  decide (0 < p ∧ old.size = N + 1 ∧ new.size = N + 1) &&
    (List.range (N + 1)).all
      (fun h ↦
        decide (new.getD h 0 = if p ≤ h then old.getD h 0 + new.getD (h - p) 0 else old.getD h 0))

/-- A successful row check yields its positive weight and all update equations
on the declared budget range. This turns a finite Boolean certificate into
the hypotheses of the recurrence soundness theorem. -/
theorem weightedPrimeRowCheck_sound (p N : ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowCheck p N old new = true) :
    0 < p ∧
      ∀ h ≤ N,
        new.getD h 0 = if p ≤ h then old.getD h 0 + new.getD (h - p) 0 else old.getD h 0 := by
  have hpairs := (Bool.and_eq_true _ _).mp hc
  have hp := (of_decide_eq_true hpairs.1).1
  refine ⟨hp, ?_⟩
  intro h hh
  have hm : h ∈ List.range (N + 1) := List.mem_range.mpr (Nat.lt_succ_iff.mpr hh)
  exact of_decide_eq_true ((List.all_eq_true.mp hpairs.2) h hm)

/-- A checked update transforms a correct old row into a correct new row
through `N`. The finite checker supplies the recurrence equations and the
abstract row theorem supplies induction on the budget. -/
theorem weightedPrimeRow_correct (p N : ℕ) (ps : List ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowCheck p N old new = true)
    (hold : ∀ h ≤ N, old.getD h 0 = weightedPrimeCount id ps h) :
    ∀ h ≤ N, new.getD h 0 = weightedPrimeCount id (p :: ps) h :=
  weightedPrimeCount_row_sound p ps (fun h ↦ old.getD h 0) (fun h ↦ new.getD h 0) N
    (weightedPrimeRowCheck_sound p N old new hc).1 hold
    (weightedPrimeRowCheck_sound p N old new hc).2

/-- Check that the base row has the declared length and equals one at every
budget. It represents the empty weight list, for which only the empty product
is counted. -/
def weightedPrimeBaseCheck (N : ℕ) (row : Array ℕ) : Bool :=
  decide (row.size = N + 1) && (List.range (N + 1)).all (fun h ↦ decide (row.getD h 0 = 1))

/-- Check a complete table whose first row corresponds to the full weight
list and whose final row is the all-one base row. Each intervening row must
pass the positive-weight update check against the next row. -/
def weightedPrimeTableCheck (N : ℕ) : List ℕ → List (Array ℕ) → Bool
  | [], [row] => weightedPrimeBaseCheck N row
  | p :: ps, row :: (old :: rows) =>
    weightedPrimeRowCheck p N old row && weightedPrimeTableCheck N ps (old :: rows)
  | _, _ => false

/-- A successfully checked table gives the recurrence count in its first row
at every budget through `N`. Induction over rows uses the checked base and
the row-soundness theorem, including each row's in-place dependency. -/
theorem weightedPrimeTableCheck_sound (N : ℕ) (weights : List ℕ) :
    ∀ (row : Array ℕ) (rows : List (Array ℕ)),
      weightedPrimeTableCheck N weights (row :: rows) = true →
        ∀ h ≤ N, row.getD h 0 = weightedPrimeCount id weights h := by
  induction weights with
  | nil =>
    intro row rows hc h hh
    cases rows with
    | cons r rs => contradiction
    | nil =>
      have hpairs := (Bool.and_eq_true _ _).mp hc
      have hm : h ∈ List.range (N + 1) := List.mem_range.mpr (Nat.lt_succ_iff.mpr hh)
      have hval := of_decide_eq_true ((List.all_eq_true.mp hpairs.2) h hm)
      rw [weightedPrimeCount.eq_def]
      exact hval
  | cons p ps ih =>
    intro row rows hc
    cases rows with
    | nil => contradiction
    | cons old rest =>
      have hc' := (Bool.and_eq_true _ _).mp hc
      exact weightedPrimeRow_correct p N ps old row hc'.1 (ih old rest hc'.2)

end PseudoPrime.PrimeTestBounds.MillerRabin
