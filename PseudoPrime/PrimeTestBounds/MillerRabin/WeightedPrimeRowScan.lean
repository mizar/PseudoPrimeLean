/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeRowScanCheck

/-! # Soundness of a streaming row checker -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonempty list's first entry is the first entry of its array. -/
private theorem array_cons_zero (a : ℕ) (xs : List ℕ) : (a :: xs).toArray.getD 0 0 = a := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_zero,
    Option.getD_some]

/-- Converting a tail preserves its entries at successor positions. -/
private theorem array_cons_succ (a i : ℕ) (xs : List ℕ) :
    (a :: xs).toArray.getD (i + 1) 0 = xs.toArray.getD i 0 := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_cons_succ]

/-- Each position in a successful scan satisfies its corresponding update. -/
private theorem scanRow_sound {old new delayed : List ℕ}
    (hc : weightedPrimeScanRow old new delayed = true) :
    ∀ i,
      i < old.length → new.toArray.getD i 0 = old.toArray.getD i 0 + delayed.toArray.getD i 0 := by
  induction old generalizing new delayed with
  | nil =>
    intro i hi
    exact (Nat.not_lt_zero i hi).elim
  | cons a old ih =>
    cases new with
    | nil => cases delayed <;> cases hc
    | cons b new =>
      cases delayed with
      | nil => cases hc
      | cons c delayed =>
        have hs := (Bool.and_eq_true _ _).mp hc
        have heq : b = a + c := of_decide_eq_true hs.1
        intro i hi
        cases i with
        | zero => simpa only [array_cons_zero] using heq
        | succ i =>
          simp only [array_cons_succ]
          apply ih hs.2 i
          exact Nat.lt_of_succ_lt_succ hi

/-- The array of a zero-padded row agrees with the shifted array entry. -/
private theorem delayed_array (p i : ℕ) (xs : List ℕ) :
    (List.replicate p 0 ++ xs).toArray.getD i 0 =
      if p ≤ i then xs.toArray.getD (i - p) 0 else 0 := by
  simp only [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_append,
    List.length_replicate, List.getElem?_replicate]
  by_cases h : p ≤ i
  · simp only [Nat.not_lt.mpr h, ite_false, ite_eq_left h]
  · have hi : i < p := Nat.lt_of_not_ge h
    simp only [hi, ite_true, ite_eq_right h, Option.getD_some]

/--
A successful scan of equal-sized rows gives every weighted-count recurrence.
The proof follows the three lists simultaneously and relates the delayed row to the shifted index.
-/
theorem weightedPrimeRowScan_sound (p N : ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowScanCheck p N old new = true) :
    0 < p ∧
      ∀ h ≤ N,
        new.getD h 0 = if p ≤ h then old.getD h 0 + new.getD (h - p) 0 else old.getD h 0 := by
  have hs := (Bool.and_eq_true _ _).mp hc
  have hp := of_decide_eq_true hs.1
  refine ⟨hp.1, ?_⟩
  intro h hh
  have hi : h < old.toList.length := by
    rw [Array.length_toList, hp.2.1]
    exact Nat.lt_succ_of_le hh
  have heq := scanRow_sound hs.2 h hi
  rw [delayed_array, Array.toArray_toList] at heq
  by_cases hph : p ≤ h
  · simpa only [ite_eq_left hph] using heq
  · simpa only [ite_eq_right hph, Nat.add_zero] using heq

/-- A successful streaming check passes the existing indexed checker.
This compatibility theorem permits existing row certificates to use the faster scan. -/
theorem weightedPrimeRowScan_indexed (p N : ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowScanCheck p N old new = true) :
    weightedPrimeRowCheck p N old new = true := by
  have hs := weightedPrimeRowScan_sound p N old new hc
  have hsize := of_decide_eq_true ((Bool.and_eq_true _ _).mp hc).1
  unfold weightedPrimeRowCheck
  apply (Bool.and_eq_true _ _).mpr
  constructor
  · exact decide_eq_true hsize
  · apply List.all_eq_true.mpr
    intro h hh
    exact decide_eq_true (hs.2 h (Nat.lt_succ_iff.mp (List.mem_range.mp hh)))

end PseudoPrime.PrimeTestBounds.MillerRabin
