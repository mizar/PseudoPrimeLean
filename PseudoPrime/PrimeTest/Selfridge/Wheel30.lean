/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import PseudoPrime.PrimeTest.Selfridge.Candidates
import PseudoPrime.PrimeTest.Selfridge.Composite
import Mathlib.Tactic

/-!
# Wheel30 candidate arithmetic for PrimeTest

This module proves the elementary relationship between the Wheel30 candidate predicates and
odd prime candidates.  It is independent of `PseudoSquare` and GRH.
-/

namespace PseudoPrime.PrimeTest

/-- Every factor-detecting Wheel30 candidate is a classical candidate. -/
theorem wheel30NeOneCandidate_classical {i : ℕ} (hi : isWheel30NeOneCandidate i) :
    isClassicalCandidate i := by exact isWheel30NeOneCandidate_isClassical hi

/-- Every pure `-1` Wheel30 candidate is a classical candidate. -/
theorem wheel30NegOneCandidate_classical {i : ℕ} (hi : isWheel30NegOneCandidate i) :
    isClassicalCandidate i := by exact isWheel30NegOneCandidate_isClassical hi

/-- Every odd prime at least `5` belongs to both Wheel30 candidate sets. This private theorem
contains the shared prime and residue argument used by the two public membership results. -/
private theorem prime_mem_wheel30Candidates {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp5 : 5 ≤ p) :
    isWheel30NeOneCandidate p ∧ isWheel30NegOneCandidate p := by
  unfold isWheel30NeOneCandidate isWheel30NegOneCandidate
  by_cases hpeq5 : p = 5
  · subst p
    constructor
    · norm_num only [isWheel30NeOneInitial, isWheel30TailResidue, false_or, true_or, false_and,
        or_false]
    · norm_num only [isWheel30NegOneInitial, isWheel30TailResidue, false_or, true_or, false_and,
        or_false]
  · have hpmod2 : p % 2 = 1 := Nat.odd_iff.mp hpodd
    have hpmod3 : p % 3 ≠ 0 := by
      intro hmod
      have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h
      · norm_num only at h
      · have hp5' : 5 ≤ 3 := by simpa only [← h] using hp5
        exact Nat.not_le_of_gt (by decide : 3 < 5) hp5'
    have hpmod5 : p % 5 ≠ 0 := by
      intro hmod
      have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hmod
      rcases hp.eq_one_or_self_of_dvd 5 hdvd with h | h
      · norm_num only at h
      · exact hpeq5 h.symm
    by_cases hp29 : p ≤ 29
    · have hne : isWheel30NeOneInitial p := by
        unfold isWheel30NeOneInitial
        interval_cases p <;> norm_num only [Nat.reduceMod] at * <;>
          simp only [or_false, or_true] at *
      have hneg : isWheel30NegOneInitial p := by
        unfold isWheel30NegOneInitial
        interval_cases p <;> norm_num only [Nat.reduceMod] at * <;>
          simp only [or_false, or_true] at *
      exact ⟨Or.inl hne, Or.inl hneg⟩
    · have hmod2' : (p % 30) % 2 = 1 := by
        rw [Nat.mod_mod_of_dvd p (by decide : 2 ∣ 30)]
        exact hpmod2
      have hmod3' : (p % 30) % 3 ≠ 0 := by
        rw [Nat.mod_mod_of_dvd p (by decide : 3 ∣ 30)]
        exact hpmod3
      have hmod5' : (p % 30) % 5 ≠ 0 := by
        rw [Nat.mod_mod_of_dvd p (by decide : 5 ∣ 30)]
        exact hpmod5
      have hlt30 : p % 30 < 30 := Nat.mod_lt p (by norm_num only : 0 < 30)
      have htail : isWheel30TailResidue p := by
        unfold isWheel30TailResidue
        interval_cases h : p % 30 <;> norm_num only [h, Nat.reduceMod] at * <;>
          simp only [or_false, or_true] at *
      exact ⟨Or.inr ⟨Nat.lt_of_not_ge hp29, htail⟩, Or.inr ⟨Nat.lt_of_not_ge hp29, htail⟩⟩

/-- Every odd prime at least `5` belongs to the factor-detecting Wheel30 candidates. -/
theorem prime_mem_wheel30NeOneCandidate {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp5 : 5 ≤ p) :
    isWheel30NeOneCandidate p :=
  (prime_mem_wheel30Candidates hp hpodd hp5).1

/-- Every odd prime at least `5` belongs to the pure `-1` Wheel30 candidates. -/
theorem prime_mem_wheel30NegOneCandidate {p : ℕ} (hp : p.Prime) (hpodd : Odd p) (hp5 : 5 ≤ p) :
    isWheel30NegOneCandidate p :=
  (prime_mem_wheel30Candidates hp hpodd hp5).2

/-- For a positive odd nonsquare input, the classical and Wheel30 factor-detecting first-stops
agree. -/
theorem firstStopNeOne_wheel30_eq_classical {n : ℕ} (hnpos : 0 < n) (hn : Odd n) (hns : ¬IsSquare n)
    (hclass : (FirstStopNeOneSet isClassicalCandidate n).Nonempty)
    (hwheel : (FirstStopNeOneSet isWheel30NeOneCandidate n).Nonempty) :
    firstStopNeOne isWheel30NeOneCandidate n hwheel =
      firstStopNeOne isClassicalCandidate n hclass := by
  apply Nat.le_antisymm
  · have hstop := firstStopNeOne_mem isClassicalCandidate n hclass
    have hcand : isWheel30NeOneCandidate (firstStopNeOne isClassicalCandidate n hclass) := by
      by_cases hp : (firstStopNeOne isClassicalCandidate n hclass).Prime
      · exact prime_mem_wheel30NeOneCandidate hp hstop.1.2 hstop.1.1
      · have hi : 0 < firstStopNeOne isClassicalCandidate n hclass := by
          have hi5 := hstop.1.1
          exact Nat.lt_of_lt_of_le (by decide : 0 < 5) hi5
        have hmin :
          ∀ j < firstStopNeOne isClassicalCandidate n hclass,
            j ∉ FirstStopNeOneSet isClassicalCandidate n := by
          intro j hj
          exact not_mem_firstStopNeOneSet_of_lt isClassicalCandidate n hclass hj
        rcases
          composite_minimal_classical_neOne_eq_nine_or_fifteen hnpos hn hns hi hp hstop hmin with
          h | h
        · rw [h]
          norm_num only [isWheel30NeOneCandidate, isWheel30NeOneInitial, isWheel30TailResidue,
            false_or, true_or, false_and, or_false]
        · rw [h]
          norm_num only [isWheel30NeOneCandidate, isWheel30NeOneInitial, isWheel30TailResidue,
            false_or, true_or, false_and, or_false]
    exact firstStopNeOne_le isWheel30NeOneCandidate n hwheel ⟨hcand, hstop.2.1, hstop.2.2⟩
  · have hstop := firstStopNeOne_mem isWheel30NeOneCandidate n hwheel
    exact
      firstStopNeOne_le isClassicalCandidate n hclass
        ⟨wheel30NeOneCandidate_classical hstop.1, hstop.2.1, hstop.2.2⟩

/-- For an odd input, the classical and Wheel30 pure `-1` first-stops agree. -/
theorem firstStopNegOne_wheel30_eq_classical {n : ℕ} (hn : Odd n)
    (hclass : (FirstStopNegOneSet isClassicalCandidate n).Nonempty)
    (hwheel : (FirstStopNegOneSet isWheel30NegOneCandidate n).Nonempty) :
    firstStopNegOne isWheel30NegOneCandidate n hwheel =
      firstStopNegOne isClassicalCandidate n hclass := by
  apply Nat.le_antisymm
  · have hstop := firstStopNegOne_mem isClassicalCandidate n hclass
    have hcand : isWheel30NegOneCandidate (firstStopNegOne isClassicalCandidate n hclass) := by
      by_cases hp : (firstStopNegOne isClassicalCandidate n hclass).Prime
      · exact prime_mem_wheel30NegOneCandidate hp hstop.1.2 hstop.1.1
      · have hi : 0 < firstStopNegOne isClassicalCandidate n hclass := by
          have hi5 := hstop.1.1
          exact Nat.lt_of_lt_of_le (by decide : 0 < 5) hi5
        have hmin :
          ∀ j < firstStopNegOne isClassicalCandidate n hclass,
            j ∉ FirstStopNegOneSet isClassicalCandidate n := by
          intro j hj
          exact not_mem_firstStopNegOneSet_of_lt isClassicalCandidate n hclass hj
        rcases
          composite_minimal_classical_negOne_eq_fifteen_or_twenty_one_or_twenty_seven hn hi hp hstop
            hmin with
          h | h | h
        · rw [h]
          norm_num only [isWheel30NegOneCandidate, isWheel30NegOneInitial, isWheel30TailResidue,
            false_or, true_or, false_and, or_false]
        · rw [h]
          norm_num only [isWheel30NegOneCandidate, isWheel30NegOneInitial, isWheel30TailResidue,
            false_or, true_or, false_and, or_false]
        · rw [h]
          norm_num only [isWheel30NegOneCandidate, isWheel30NegOneInitial, isWheel30TailResidue,
            false_or, true_or, false_and, or_false]
    exact firstStopNegOne_le isWheel30NegOneCandidate n hwheel ⟨hcand, hstop.2⟩
  · have hstop := firstStopNegOne_mem isWheel30NegOneCandidate n hwheel
    exact
      firstStopNegOne_le isClassicalCandidate n hclass
        ⟨wheel30NegOneCandidate_classical hstop.1, hstop.2⟩

end PseudoPrime.PrimeTest
