/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Finset.Lattice.Fold
import PseudoPrime.PseudoSquare.Bounds.WitnessMaximum
import PseudoPrime.PseudoSquare.Computation.QThresholds
import PseudoPrime.PrimeTest.Selfridge.Nonempty
import PseudoPrime.PrimeTest.Selfridge.WitnessBounds
import PseudoPrime.PrimeTest.Selfridge.Wheel30

/-!
# Finite maxima of Selfridge stopping positions

This file lifts the pointwise equality of the classical and Wheel30 pure `-1` scans to the
finite admissible domain.  Nonemptiness of every stopping set is supplied internally by the
odd-nonsquare theorem, so the aggregate definitions need no proof arguments from callers.
-/

namespace PseudoPrime.SelfridgeBoundGrh

/-- The largest classical factor-detecting first-stop on the admissible domain up to `B`. -/
noncomputable def classicalNeOneMaximum (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n.val
        (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/-- The largest factor-detecting Wheel30 first-stop on the admissible domain up to `B`. -/
noncomputable def wheel30NeOneMaximum (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      PrimeTest.firstStopNeOne PrimeTest.isWheel30NeOneCandidate n.val
        (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/--
The largest classical pure `-1` first-stop among admissible inputs up to `B`.  The finite supremum
is `0` when the admissible set is empty.
-/
noncomputable def classicalNegOneMaximum (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n.val
        (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/--
The largest Wheel30 pure `-1` first-stop among admissible inputs up to `B`.  The finite supremum
is `0` when the admissible set is empty.
-/
noncomputable def wheel30NegOneMaximum (B : ℕ) : ℕ := by
  classical
    exact
    (NumberTheory.admissibleFinset B).attach.sup fun n =>
      PrimeTest.firstStopNegOne PrimeTest.isWheel30NegOneCandidate n.val
        (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).odd)
          ((NumberTheory.mem_admissibleFinset_iff.mp n.property).not_isSquare))

/--
The Wheel30 and classical pure `-1` maxima agree on every finite admissible domain.  The proof
applies the pointwise first-stop equality to each attached member before taking the supremum.
-/
theorem wheel30NegOneMaximum_eq_classicalNegOneMaximum (B : ℕ) :
    wheel30NegOneMaximum B = classicalNegOneMaximum B := by
  classical
  unfold wheel30NegOneMaximum classicalNegOneMaximum
  apply Finset.sup_congr rfl
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  exact
    PrimeTest.firstStopNegOne_wheel30_eq_classical hn.odd
      (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)
      (PrimeTest.wheel30FirstStopNegOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)

/-- The Wheel30 and classical factor-detecting maxima agree on every admissible domain. -/
theorem wheel30NeOneMaximum_eq_classicalNeOneMaximum (B : ℕ) :
    wheel30NeOneMaximum B = classicalNeOneMaximum B := by
  classical
  unfold wheel30NeOneMaximum classicalNeOneMaximum
  apply Finset.sup_congr rfl
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  exact
    PrimeTest.firstStopNeOne_wheel30_eq_classical hn.pos hn.odd hn.not_isSquare
      (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)
      (PrimeTest.wheel30FirstStopNeOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)

/--
The classical factor-detecting maximum is bounded by the classical pure `-1` maximum: the same
candidate predicate is used for both stopping rules, so the pointwise "first-stop inclusion"
(`PrimeTest.firstStopNeOne_le_firstStopNegOne_same_candidates`) lifts to the finite supremum.
-/
theorem classicalNeOneMaximum_le_classicalNegOneMaximum (B : ℕ) :
    classicalNeOneMaximum B ≤ classicalNegOneMaximum B := by
  classical
  unfold classicalNeOneMaximum classicalNegOneMaximum
  apply Finset.sup_mono_fun
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  have hne1 : n.val ≠ 1 := by
    intro h
    exact hn.not_isSquare (h ▸ ⟨1, rfl⟩)
  have hn1 : 1 < n.val := by
    have := hn.pos; omega
  exact
    PrimeTest.firstStopNeOne_le_firstStopNegOne_same_candidates hn1
      (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)

/-- The least-prime `≠ 1` maximum is bounded by the classical first-stop maximum. -/
theorem QNeOne_le_classicalNeOneMaximum (B : ℕ) :
    PseudoSquare.QNeOne B ≤ classicalNeOneMaximum B := by
  classical
  unfold PseudoSquare.QNeOne classicalNeOneMaximum
  apply Finset.sup_mono_fun
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  exact
    (PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos
        hn.odd hn.not_isSquare _ _).1

/-- The classical `≠ 1` maximum is at most `max 15 PseudoPrime.PseudoSquare.QNeOne`. -/
theorem classicalNeOneMaximum_le_max_fifteen_QNeOne (B : ℕ) :
    classicalNeOneMaximum B ≤ max 15 (PseudoSquare.QNeOne B) := by
  classical
  unfold classicalNeOneMaximum
  apply Finset.sup_le
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  have hpoint :=
    PrimeTest.primeNeOneWitness_le_classicalFirstStop_le_max_unconditional hn.pos hn.odd
      hn.not_isSquare
      (PrimeTest.primeNeOneWitnessSet_nonempty_of_negOne
        (PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn.odd
          hn.not_isSquare))
      (PrimeTest.classicalFirstStopNeOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)
  exact
    hpoint.2.trans
      (max_le_max_left 15 (PseudoSquare.primeNeOneWitness_le_QNeOne n.property))

/-- Once `PseudoSquare.QNeOne` exceeds `15`, the classical maximum agrees with it permanently. -/
theorem classicalNeOneMaximum_eq_QNeOne_of_fifteen_lt {B : ℕ}
    (hB : 15 < PseudoSquare.QNeOne B) :
    classicalNeOneMaximum B = PseudoSquare.QNeOne B := by
  apply Nat.le_antisymm
  · rw [← max_eq_right hB.le]
    exact classicalNeOneMaximum_le_max_fifteen_QNeOne B
  · exact QNeOne_le_classicalNeOneMaximum B

/-- The Wheel30 `≠ 1` maximum also equals `PseudoSquare.QNeOne` once the latter exceeds `15`. -/
theorem wheel30NeOneMaximum_eq_QNeOne_of_fifteen_lt {B : ℕ}
    (hB : 15 < PseudoSquare.QNeOne B) :
    wheel30NeOneMaximum B = PseudoSquare.QNeOne B := by
  rw [wheel30NeOneMaximum_eq_classicalNeOneMaximum]
  exact classicalNeOneMaximum_eq_QNeOne_of_fifteen_lt hB

/-- The least-prime `-1` maximum is bounded by the classical pure first-stop maximum. -/
theorem QNegOne_le_classicalNegOneMaximum (B : ℕ) :
    PseudoSquare.QNegOne B ≤ classicalNegOneMaximum B := by
  classical
  unfold PseudoSquare.QNegOne classicalNegOneMaximum
  apply Finset.sup_mono_fun
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  exact (PrimeTest.primeNegOneWitness_le_classicalFirstStop_le_max hn.odd _ _).1

/-- The classical pure `-1` maximum is at most `max 27 PseudoPrime.PseudoSquare.QNegOne`. -/
theorem classicalNegOneMaximum_le_max_twenty_seven_QNegOne (B : ℕ) :
    classicalNegOneMaximum B ≤ max 27 (PseudoSquare.QNegOne B) := by
  classical
  unfold classicalNegOneMaximum
  apply Finset.sup_le
  intro n _
  have hn := NumberTheory.mem_admissibleFinset_iff.mp n.property
  have hpoint :=
    PrimeTest.primeNegOneWitness_le_classicalFirstStop_le_max hn.odd
      (PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare hn.odd hn.not_isSquare)
      (PrimeTest.classicalFirstStopNegOneSet_nonempty_of_odd_nonsquare hn.odd
        hn.not_isSquare)
  exact
    hpoint.2.trans
      (max_le_max_left 27 (PseudoSquare.primeNegOneWitness_le_QNegOne n.property))

/-- Once `PseudoSquare.QNegOne` exceeds `27`, the classical and Wheel30 pure maxima equal it. -/
theorem classicalNegOneMaximum_eq_QNegOne_of_twenty_seven_lt {B : ℕ}
    (hB : 27 < PseudoSquare.QNegOne B) :
    classicalNegOneMaximum B = PseudoSquare.QNegOne B := by
  apply Nat.le_antisymm
  · rw [← max_eq_right hB.le]
    exact classicalNegOneMaximum_le_max_twenty_seven_QNegOne B
  · exact QNegOne_le_classicalNegOneMaximum B

/-- The Wheel30 pure maximum also equals `PseudoSquare.QNegOne` once the latter exceeds `27`. -/
theorem wheel30NegOneMaximum_eq_QNegOne_of_twenty_seven_lt {B : ℕ}
    (hB : 27 < PseudoSquare.QNegOne B) :
    wheel30NegOneMaximum B = PseudoSquare.QNegOne B := by
  rw [wheel30NegOneMaximum_eq_classicalNegOneMaximum]
  exact classicalNegOneMaximum_eq_QNegOne_of_twenty_seven_lt hB

/-- The pure `-1` classical maximum equals `QNegOne` once the admissible range reaches `399`. -/
theorem classicalNegOneMaximum_eq_QNegOne_of_399_le {B : ℕ} (hB : 399 ≤ B) :
    classicalNegOneMaximum B = PseudoSquare.QNegOne B := by
  exact
    classicalNegOneMaximum_eq_QNegOne_of_twenty_seven_lt
      (PseudoSquare.twenty_seven_lt_QNegOne_of_399_le hB)

/-- The input `751` keeps `QNeOne` above `15` at every later bound. -/
theorem fifteen_lt_QNeOne_of_751_le {B : ℕ} (hB : 751 ≤ B) :
    15 < PseudoSquare.QNeOne B := by
  have hadm : 751 ∈ NumberTheory.admissibleFinset B := by
    apply NumberTheory.mem_admissibleFinset_iff.mpr
    exact ⟨by norm_num only, hB, by decide, PseudoSquare.not_isSquare_751⟩
  have hw : (PrimeTest.PrimeNeOneWitnessSet 751).Nonempty :=
    PrimeTest.primeNeOneWitnessSet_nonempty_of_negOne
      (PrimeTest.primeNegOneWitnessSet_nonempty_of_odd_nonsquare (by decide)
        PseudoSquare.not_isSquare_751)
  have hle := PseudoSquare.primeNeOneWitness_le_QNeOne hadm
  rw [PseudoSquare.primeNeOneWitness_751_eq_17 hw] at hle
  omega

/-- The Wheel30 pure `-1` maximum equals `QNegOne` from `399` onward. -/
theorem wheel30NegOneMaximum_eq_QNegOne_of_399_le {B : ℕ} (hB : 399 ≤ B) :
    wheel30NegOneMaximum B = PseudoSquare.QNegOne B := by
  exact
    wheel30NegOneMaximum_eq_QNegOne_of_twenty_seven_lt
      (PseudoSquare.twenty_seven_lt_QNegOne_of_399_le hB)

/-- The classical and Wheel30 factor-detecting maxima equal `QNeOne` from `751` onward. -/
theorem classicalNeOneMaximum_eq_QNeOne_of_751_le {B : ℕ} (hB : 751 ≤ B) :
    classicalNeOneMaximum B = PseudoSquare.QNeOne B := by
  exact classicalNeOneMaximum_eq_QNeOne_of_fifteen_lt (fifteen_lt_QNeOne_of_751_le hB)

theorem wheel30NeOneMaximum_eq_QNeOne_of_751_le {B : ℕ} (hB : 751 ≤ B) :
    wheel30NeOneMaximum B = PseudoSquare.QNeOne B := by
  exact wheel30NeOneMaximum_eq_QNeOne_of_fifteen_lt (fifteen_lt_QNeOne_of_751_le hB)

end PseudoPrime.SelfridgeBoundGrh
