/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeRowScanCheck
import Mathlib.Data.List.GetD

/-! # Soundness of a streaming row checker -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Each position in a successful scan satisfies its corresponding update. -/
private theorem scanRow_sound {old new delayed : List ℕ}
    (hc : weightedPrimeScanRow old new delayed = true) :
    ∀ i, i < old.length → new.getD i 0 = old.getD i 0 + delayed.getD i 0 := by
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
        | zero => simpa only [List.getD_cons_zero] using heq
        | succ i =>
          simp only [List.getD_cons_succ]
          apply ih hs.2 i
          exact Nat.lt_of_succ_lt_succ hi

/-- The zero-padded delayed row agrees with the shifted row entry. -/
private theorem delayed_getD (p i : ℕ) (xs : List ℕ) :
    (List.replicate p 0 ++ xs).getD i 0 = if p ≤ i then xs.getD (i - p) 0 else 0 := by
  by_cases h : p ≤ i
  · simp only [ite_eq_left h]
    rw [List.getD_append_right _ _ _ _ (by simpa only [List.length_replicate] using h),
      List.length_replicate]
  · simp only [ite_eq_right h]
    have hi : i < p := Nat.lt_of_not_ge h
    rw [List.getD_append _ _ _ _ (by simpa only [List.length_replicate] using hi)]
    exact List.getD_replicate 0 hi

/-- List and array default access agree for the same array. -/
private theorem array_list_getD (a : Array ℕ) (n : ℕ) : a.toList.getD n 0 = a.getD n 0 := by
  simp only [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]

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
  rw [delayed_getD, array_list_getD, array_list_getD, array_list_getD] at heq
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
