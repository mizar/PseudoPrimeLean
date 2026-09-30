/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring

/-!
# Selfridge candidate values

This executable-facing candidate layer is independent of GRH, LLS, and the
analytic `PseudoSquare` development.
-/

namespace PseudoPrime.PrimeTest

/-- The signed Selfridge value attached to an unsigned odd candidate. -/
def selfridgeD (i : ℕ) : ℤ :=
  if i % 4 = 1 then (i : ℤ) else -(i : ℤ)

/-- The classical Selfridge candidate predicate. -/
def isClassicalCandidate (i : ℕ) : Prop :=
  5 ≤ i ∧ Odd i

/-- The executable classical Selfridge candidate predicate. -/
def classicalCandidate (i : ℕ) : Bool :=
  decide (5 ≤ i) && decide (i % 2 = 1)

/-- The signed value is positive on candidates congruent to `1` modulo `4`. -/
theorem selfridgeD_of_mod_four_eq_one {i : ℕ} (hi : i % 4 = 1) : selfridgeD i = (i : ℤ) := by
  simp only [selfridgeD, hi, ite_true]

/-- The signed value is negative on candidates congruent to `3` modulo `4`. -/
theorem selfridgeD_of_mod_four_eq_three {i : ℕ} (hi : i % 4 = 3) : selfridgeD i = -(i : ℤ) := by
  have hne : i % 4 ≠ 1 :=
    Nat.ne_of_gt
      (by
        rw [hi]; decide)
  simp only [selfridgeD, hne, ite_false]

/-- The absolute value of a signed Selfridge value is its magnitude. -/
theorem selfridgeD_natAbs (i : ℕ) : (selfridgeD i).natAbs = i := by
  by_cases hi : i % 4 = 1
  · simp only [selfridgeD_of_mod_four_eq_one hi, Int.natAbs_natCast]
  · simp only [selfridgeD, hi, ite_false, Int.natAbs_neg, Int.natAbs_natCast]

/-- Every odd candidate yields a discriminant congruent to `1` modulo `4`. -/
theorem selfridgeD_methodA_mod_four {i : ℕ} (hi : Odd i) : (1 - selfridgeD i) % 4 = 0 := by
  have hi2 : i % 2 = 1 := Nat.odd_iff.mp hi
  rcases Nat.odd_mod_four_iff.mp hi2 with hi1 | hi3
  · rw [selfridgeD_of_mod_four_eq_one hi1]
    have hdecomp := Nat.mod_add_div i 4
    rw [hi1] at hdecomp
    have hnat : i = 1 + 4 * (i / 4) := by simpa only [Nat.mul_comm] using hdecomp.symm
    have hcast : (i : ℤ) = 1 + 4 * (i / 4 : ℕ) := by exact_mod_cast hnat
    have hdiv : (4 : ℤ) ∣ 1 - (i : ℤ) := by
      refine ⟨-((i / 4 : ℕ) : ℤ), ?_⟩
      rw [hcast]
      ring
    exact Int.emod_eq_zero_of_dvd hdiv
  · rw [selfridgeD_of_mod_four_eq_three hi3]
    have hdecomp := Nat.mod_add_div i 4
    rw [hi3] at hdecomp
    have hnat : i = 3 + 4 * (i / 4) := by simpa only [Nat.mul_comm] using hdecomp.symm
    have hcast : (i : ℤ) = 3 + 4 * (i / 4 : ℕ) := by exact_mod_cast hnat
    have hdiv : (4 : ℤ) ∣ 1 + (i : ℤ) := by
      refine ⟨(i / 4 : ℕ) + 1, ?_⟩
      rw [hcast]
      ring
    rw [Int.sub_neg]
    exact Int.emod_eq_zero_of_dvd hdiv

/-- The executable candidate predicate agrees with its proposition. -/
theorem classicalCandidate_eq_true_iff {i : ℕ} :
    classicalCandidate i = true ↔ isClassicalCandidate i := by
  simp only [classicalCandidate, Bool.and_eq_true, decide_eq_true_eq, isClassicalCandidate]
  rw [Nat.odd_iff]

/-- The eight residue classes coprime to `30` used by the Wheel30 tail. -/
def isWheel30TailResidue (i : ℕ) : Prop :=
  i % 30 = 1 ∨
    i % 30 = 7 ∨ i % 30 = 11 ∨ i % 30 = 13 ∨ i % 30 = 17 ∨ i % 30 = 19 ∨ i % 30 = 23 ∨ i % 30 = 29

/-- Every residue class in the Wheel30 tail consists of odd numbers. -/
theorem isWheel30TailResidue_odd {i : ℕ} (hi : isWheel30TailResidue i) : Odd i := by
  have hmod : i % 2 = (i % 30) % 2 := (Nat.mod_mod_of_dvd i (by decide : 2 ∣ 30)).symm
  rcases hi with h1 | h7 | h11 | h13 | h17 | h19 | h23 | h29
  · apply Nat.odd_iff.mpr
    simpa only [h1, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h7, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h11, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h13, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h17, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h19, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h23, Nat.reduceMod] using hmod
  · apply Nat.odd_iff.mpr
    simpa only [h29, Nat.reduceMod] using hmod

/-- The exceptional initial candidates for the pure Jacobi `-1` scan. -/
def isWheel30NegOneInitial (i : ℕ) : Prop :=
  i = 5 ∨ i = 7 ∨ i = 11 ∨ i = 13 ∨ i = 15 ∨ i = 17 ∨ i = 19 ∨ i = 21 ∨ i = 23 ∨ i = 27 ∨ i = 29

/-- The Wheel30 candidates for the pure Jacobi `-1` scan. -/
def isWheel30NegOneCandidate (i : ℕ) : Prop :=
  isWheel30NegOneInitial i ∨ 29 < i ∧ isWheel30TailResidue i

/-- The exceptional initial candidates for the factor-detecting Wheel30 scan. -/
def isWheel30NeOneInitial (i : ℕ) : Prop :=
  i = 5 ∨ i = 7 ∨ i = 9 ∨ i = 11 ∨ i = 13 ∨ i = 15 ∨ i = 17 ∨ i = 19 ∨ i = 23 ∨ i = 29

/-- The Wheel30 candidates for the factor-detecting `≠ 1` scan. -/
def isWheel30NeOneCandidate (i : ℕ) : Prop :=
  isWheel30NeOneInitial i ∨ 29 < i ∧ isWheel30TailResidue i

/-- The executable Wheel30 candidate predicate for the pure Jacobi `-1` scan. -/
def wheel30NegOneCandidate (i : ℕ) : Bool :=
  (decide (i = 5) || decide (i = 7) || decide (i = 11) || decide (i = 13) || decide (i = 15) ||
      decide (i = 17) ||
      decide (i = 19) ||
      decide (i = 21) ||
      decide (i = 23) ||
      decide (i = 27) ||
      decide (i = 29)) ||
    (decide (29 < i) &&
      (decide (i % 30 = 1) || decide (i % 30 = 7) || decide (i % 30 = 11) || decide (i % 30 = 13) ||
        decide (i % 30 = 17) ||
        decide (i % 30 = 19) ||
        decide (i % 30 = 23) ||
        decide (i % 30 = 29)))

/-- The executable Wheel30 candidate predicate agrees with its proposition. -/
theorem wheel30NegOneCandidate_eq_true_iff {i : ℕ} :
    wheel30NegOneCandidate i = true ↔ isWheel30NegOneCandidate i := by
  simp only [wheel30NegOneCandidate, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    isWheel30NegOneCandidate, isWheel30NegOneInitial, isWheel30TailResidue, or_assoc]

/-- The executable factor-detecting Wheel30 candidate predicate. -/
def wheel30NeOneCandidate (i : ℕ) : Bool :=
  (decide (i = 5) || decide (i = 7) || decide (i = 9) || decide (i = 11) || decide (i = 13) ||
      decide (i = 15) ||
      decide (i = 17) ||
      decide (i = 19) ||
      decide (i = 23) ||
      decide (i = 29)) ||
    (decide (29 < i) &&
      (decide (i % 30 = 1) || decide (i % 30 = 7) || decide (i % 30 = 11) || decide (i % 30 = 13) ||
        decide (i % 30 = 17) ||
        decide (i % 30 = 19) ||
        decide (i % 30 = 23) ||
        decide (i % 30 = 29)))

/-- The executable factor-detecting Wheel30 predicate agrees with its proposition. -/
theorem wheel30NeOneCandidate_eq_true_iff {i : ℕ} :
    wheel30NeOneCandidate i = true ↔ isWheel30NeOneCandidate i := by
  simp only [wheel30NeOneCandidate, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    isWheel30NeOneCandidate, isWheel30NeOneInitial, isWheel30TailResidue, or_assoc]

/-- Every factor-detecting Wheel30 candidate is a classical Selfridge candidate. -/
theorem isWheel30NeOneCandidate_isClassical {i : ℕ} (hi : isWheel30NeOneCandidate i) :
    isClassicalCandidate i := by
  rcases hi with hi | ⟨hi29, hires⟩
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  · refine ⟨Nat.le_of_lt (Nat.lt_trans (by decide : 5 < 29) hi29), ?_⟩
    exact isWheel30TailResidue_odd hires

/-- Every Wheel30 pure `-1` candidate is a classical Selfridge candidate. -/
theorem isWheel30NegOneCandidate_isClassical {i : ℕ} (hi : isWheel30NegOneCandidate i) :
    isClassicalCandidate i := by
  rcases hi with hi | ⟨hi29, hires⟩
  · rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by decide, by decide⟩
  · refine ⟨Nat.le_of_lt (Nat.lt_trans (by decide : 5 < 29) hi29), ?_⟩
    exact isWheel30TailResidue_odd hires

end PseudoPrime.PrimeTest
