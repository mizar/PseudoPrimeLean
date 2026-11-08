/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountGroup
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Grouped counts on a scaled budget grid -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Add `m` equal-weight labels to a base count on a budget grid. The index
`k` counts available units of the common weight, and the recurrence separates
multisets according to whether they contain the first new label. -/
def weightedGroupGrid (base : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, k => base k
  | _ + 1, 0 => base 0
  | m + 1, k + 1 => weightedGroupGrid base m (k + 1) + weightedGroupGrid base (m + 1) k

/-- With no available weight units, only the base row contributes. -/
theorem weightedGroupGrid_zero (base : ℕ → ℕ) (m : ℕ) : weightedGroupGrid base m 0 = base 0 := by
  cases m <;> simp only [weightedGroupGrid]

/-- If the base row bounds the counts at budgets `r + k*p`, the grouped
recurrence bounds the count after adding `m` labels of weight `p`. The
remainder `r < p` handles the zero-budget step. -/
theorem weightedGroupGrid_le (p r : ℕ) (ps : List ℕ) (base : ℕ → ℕ) (hp : 0 < p) (hr : r < p)
    (N : ℕ) (hbase : ∀ k ≤ N, base k ≤ weightedPrimeCount id ps (r + k * p)) :
    ∀ m k,
      k ≤ N →
        weightedGroupGrid base m k ≤
          weightedPrimeCount id (List.replicate m p ++ ps) (r + k * p) := by
  intro m
  induction m with
  | zero =>
    intro k hk
    simpa only [weightedGroupGrid, List.replicate_zero, List.nil_append] using hbase k hk
  | succ m ih =>
    intro k
    induction k with
    | zero =>
      intro hk
      simp only [weightedGroupGrid, Nat.zero_mul, Nat.add_zero, List.replicate_succ,
        List.cons_append]
      rw [weightedPrimeCount.eq_def]
      simp only [id_eq, dite_eq_left hp, dite_eq_right (Nat.not_le_of_gt hr)]
      simpa only [weightedGroupGrid_zero, Nat.zero_mul, Nat.add_zero] using ih 0 hk
    | succ k ikh =>
      intro hk
      simp only [weightedGroupGrid, List.replicate_succ, List.cons_append]
      rw [weightedPrimeCount.eq_def]
      simp only [id_eq, dite_eq_left hp]
      have hfit : p ≤ r + (k + 1) * p := by
        rw [Nat.add_mul, Nat.one_mul]
        omega
      rw [dite_eq_left hfit]
      have heq : r + (k + 1) * p - p = r + k * p := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_sub_cancel]
      rw [heq]
      exact Nat.add_le_add (ih (k + 1) hk) (ikh ((Nat.le_succ k).trans hk))

/-- A checked unit-weight row transforms an exact grouped grid row into the
next row. The finite recurrence is verified independently of its use as a
lower bound for a weighted prime count. -/
theorem weightedGroupGrid_row (base : ℕ → ℕ) (m N : ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowCheck 1 N old new = true)
    (hold : ∀ k ≤ N, old.getD k 0 = weightedGroupGrid base m k) :
    ∀ k ≤ N, new.getD k 0 = weightedGroupGrid base (m + 1) k := by
  have hstep := (weightedPrimeRowCheck_sound 1 N old new hc).2
  intro k hk
  induction k with
  | zero =>
    have hz := hstep 0 (Nat.zero_le N)
    norm_num only at hz
    rw [hz, hold 0 (Nat.zero_le N), weightedGroupGrid_zero, weightedGroupGrid_zero]
    simp only [ite_false]
  | succ k ih =>
    have hk' : k ≤ N := (Nat.le_succ k).trans hk
    have hs := hstep (k + 1) hk
    norm_num only [Nat.one_le_iff_ne_zero, Nat.succ_ne_zero, Nat.add_sub_cancel] at hs
    rw [hs, hold (k + 1) hk, ih hk']
    rw [ite_eq_left (Nat.succ_ne_zero k)]
    simp only [weightedGroupGrid]

/-- Check a finite sequence of grouped-grid rows, from the final row down to
the supplied base row. Each intermediate row obeys the unit-weight update. -/
def weightedGroupRowsCheck (N : ℕ) (base : Array ℕ) : Array ℕ → List (Array ℕ) → Bool
  | row, [] => decide (row = base)
  | row, old :: rest => weightedPrimeRowCheck 1 N old row && weightedGroupRowsCheck N base old rest

/-- A successful row-chain check computes the grouped grid of its base array
at every index through `N`. The number of updates is the tail length. -/
theorem weightedGroupRowsCheck_sound (N : ℕ) (base : Array ℕ) :
    ∀ (row : Array ℕ) (rows : List (Array ℕ)),
      weightedGroupRowsCheck N base row rows = true →
        ∀ k ≤ N, row.getD k 0 = weightedGroupGrid (fun j ↦ base.getD j 0) rows.length k := by
  intro row rows
  induction rows generalizing row with
  | nil =>
    intro hc k hk
    have heq : row = base := of_decide_eq_true hc
    subst row
    simp only [List.length_nil, weightedGroupGrid]
  | cons old rest ih =>
    intro hc k hk
    have hp := (Bool.and_eq_true _ _).mp hc
    have hold := ih old hp.2
    have hnew := weightedGroupGrid_row (fun j ↦ base.getD j 0) rest.length N old row hp.1 hold
    simpa only [List.length_cons] using hnew k hk

/-- A checked grid whose base row bounds a weighted count also bounds the
count after adding the prescribed number of equal-weight labels. -/
theorem weightedGroupRows_lower (p r N m : ℕ) (ps : List ℕ) (base row : Array ℕ)
    (rows : List (Array ℕ)) (hp : 0 < p) (hr : r < p) (hlen : rows.length = m)
    (hbase : ∀ k ≤ N, base.getD k 0 ≤ weightedPrimeCount id ps (r + k * p))
    (hrows : weightedGroupRowsCheck N base row rows = true) :
    row.getD N 0 ≤ weightedPrimeCount id (List.replicate m p ++ ps) (r + N * p) := by
  have hgrid := weightedGroupRowsCheck_sound N base row rows hrows N (le_refl N)
  rw [hlen] at hgrid
  rw [hgrid]
  exact weightedGroupGrid_le p r ps (fun k ↦ base.getD k 0) hp hr N hbase m N (le_refl N)

/-- Check that a short base grid samples a long count row at budgets
`min cap (r + k*p)` for every grid index through `N`. -/
def weightedGroupBaseCheck (p r cap N : ℕ) (row base : Array ℕ) : Bool :=
  (List.range (N + 1)).all fun k ↦ decide (base.getD k 0 = row.getD (min cap (r + k * p)) 0)

/-- A successful base-grid check gives each sampled equality. This connects
the finite grouped table to an independently certified long count row. -/
theorem weightedGroupBaseCheck_sound (p r cap N : ℕ) (row base : Array ℕ)
    (hc : weightedGroupBaseCheck p r cap N row base = true) :
    ∀ k ≤ N, base.getD k 0 = row.getD (min cap (r + k * p)) 0 := by
  intro k hk
  have hm : k ∈ List.range (N + 1) := List.mem_range.mpr (Nat.lt_succ_iff.mpr hk)
  exact of_decide_eq_true ((List.all_eq_true.mp hc) k hm)

end PseudoPrime.PrimeTestBounds.MillerRabin
