/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.Nat.Find
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import PseudoPrime.PrimeTest.Selfridge.Candidates

/-!
# Mathematical first-stop positions for PrimeTest

These definitions provide an independent specification layer for Selfridge
scans.  Executable bounded searches are defined in `Selfridge/SearchAscending.lean`.
-/

namespace PseudoPrime.PrimeTest

/-- Candidates whose signed Selfridge Jacobi value is `-1`. -/
def FirstStopNegOneSet (C : ℕ → Prop) (n : ℕ) : Set ℕ :=
  {i | C i ∧ jacobiSym (selfridgeD i) n = -1}

/-- Candidates detecting either a nontrivial factor or a Jacobi value other than `1`. -/
def FirstStopNeOneSet (C : ℕ → Prop) (n : ℕ) : Set ℕ :=
  {i | C i ∧ ¬n ∣ i ∧ jacobiSym (selfridgeD i) n ≠ 1}

/-- Membership in the pure `-1` stopping set. -/
theorem mem_firstStopNegOneSet_iff {C : ℕ → Prop} {n i : ℕ} :
    i ∈ FirstStopNegOneSet C n ↔ C i ∧ jacobiSym (selfridgeD i) n = -1 :=
  Iff.rfl

/-- Membership in the factor-detecting stopping set. -/
theorem mem_firstStopNeOneSet_iff {C : ℕ → Prop} {n i : ℕ} :
    i ∈ FirstStopNeOneSet C n ↔ C i ∧ ¬n ∣ i ∧ jacobiSym (selfridgeD i) n ≠ 1 :=
  Iff.rfl

/-- The least pure `-1` stopping candidate, assuming one exists. -/
noncomputable def firstStopNegOne (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) :
    ℕ := by classical exact Nat.find h

/-- The least factor-detecting stopping candidate, assuming one exists. -/
noncomputable def firstStopNeOne (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) :
    ℕ := by classical exact Nat.find h

/-- The pure `-1` first-stop belongs to its stopping set. -/
theorem firstStopNegOne_mem (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNegOne C n h ∈ FirstStopNegOneSet C n := by classical exact Nat.find_spec h

/-- The factor-detecting first-stop belongs to its stopping set. -/
theorem firstStopNeOne_mem (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) :
    firstStopNeOne C n h ∈ FirstStopNeOneSet C n := by classical exact Nat.find_spec h

/-- Every pure `-1` stopping candidate is at least the first-stop. -/
theorem firstStopNegOne_le (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) {i : ℕ}
    (hi : i ∈ FirstStopNegOneSet C n) : firstStopNegOne C n h ≤ i := by
  classical exact Nat.find_min' h hi

/-- Every factor-detecting stopping candidate is at least the first-stop. -/
theorem firstStopNeOne_le (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) {i : ℕ}
    (hi : i ∈ FirstStopNeOneSet C n) : firstStopNeOne C n h ≤ i := by
  classical exact Nat.find_min' h hi

/-- No candidate below the pure `-1` first-stop is in its stopping set. -/
theorem not_mem_firstStopNegOneSet_of_lt (C : ℕ → Prop) (n : ℕ)
    (h : (FirstStopNegOneSet C n).Nonempty) {i : ℕ} (hi : i < firstStopNegOne C n h) :
    i ∉ FirstStopNegOneSet C n := by
  intro hmem
  exact (Nat.not_le_of_lt hi) (firstStopNegOne_le C n h hmem)

/-- No candidate below the factor-detecting first-stop is in its stopping set. -/
theorem not_mem_firstStopNeOneSet_of_lt (C : ℕ → Prop) (n : ℕ)
    (h : (FirstStopNeOneSet C n).Nonempty) {i : ℕ} (hi : i < firstStopNeOne C n h) :
    i ∉ FirstStopNeOneSet C n := by
  intro hmem
  exact (Nat.not_le_of_lt hi) (firstStopNeOne_le C n h hmem)

end PseudoPrime.PrimeTest
