/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Find
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import PseudoPrime.PrimeTest.Selfridge.Candidates

/-!
# Mathematical first-stop positions for PrimeTest

These definitions provide an independent specification layer for Selfridge
scans.  Executable bounded searches are defined in `Selfridge/SearchAscending.lean`.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Mathematical pure-minus-one stopping set for natural input `n` and candidate predicate `C`.
A magnitude `i` belongs exactly when `C i ∧ jacobiSym (selfridgeD i) n = -1`.
This is an independent propositional specification, not an executable scan or a fuel bound.
Its least element, when nonempty, is used to compare candidate orders and stopping rules.
-/
def FirstStopNegOneSet (C : ℕ → Prop) (n : ℕ) : Set ℕ :=
  {i | C i ∧ jacobiSym (selfridgeD i) n = -1}

/--
Mathematical factor-detecting stopping set for natural input `n` and candidate predicate `C`.
A magnitude `i` belongs exactly when `C i ∧ ¬n ∣ i ∧ jacobiSym (selfridgeD i) n ≠ 1`.
This is an independent propositional specification, not an executable scan or a fuel bound.
Its least element, when nonempty, is used to compare candidate orders and stopping rules.
-/
def FirstStopNeOneSet (C : ℕ → Prop) (n : ℕ) : Set ℕ :=
  {i | C i ∧ ¬n ∣ i ∧ jacobiSym (selfridgeD i) n ≠ 1}

/--
Expose membership in the pure-minus-one stopping set as its defining conjunction.
For any candidate predicate `C` and natural `n`, `i`, the equivalence unfolds to `C i ∧ jacobiSym
(selfridgeD i) n = -1`.
It is definitional (`Iff.rfl`), without nonemptiness or primality premises.
Membership proofs feed the first-stop leastness and executable search specifications.
-/
theorem mem_firstStopNegOneSet_iff {C : ℕ → Prop} {n i : ℕ} :
    i ∈ FirstStopNegOneSet C n ↔ C i ∧ jacobiSym (selfridgeD i) n = -1 :=
  Iff.rfl

/--
Expose membership in the factor-detecting stopping set as its defining conjunction.
For any candidate predicate `C` and natural `n`, `i`, the equivalence unfolds to `C i ∧ ¬n ∣ i ∧
jacobiSym (selfridgeD i) n ≠ 1`.
It is definitional (`Iff.rfl`), without nonemptiness or primality premises.
Membership proofs feed the first-stop leastness and executable search specifications.
-/
theorem mem_firstStopNeOneSet_iff {C : ℕ → Prop} {n i : ℕ} :
    i ∈ FirstStopNeOneSet C n ↔ C i ∧ ¬n ∣ i ∧ jacobiSym (selfridgeD i) n ≠ 1 :=
  Iff.rfl

/--
Least magnitude in the pure-minus-one stopping set for candidate predicate `C` at input `n`.
The explicit nonemptiness proof `h` guarantees a witness; `Nat.find h` selects its least value.
This noncomputable mathematical interface is independent of scan fuel and evaluation order.
Membership and leastness lemmas connect it to finite executable searches.
-/
noncomputable def firstStopNegOne (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) :
    ℕ := by classical exact Nat.find h

/--
Least magnitude in the factor-detecting stopping set for candidate predicate `C` at input `n`.
The explicit nonemptiness proof `h` guarantees a witness; `Nat.find h` selects its least value.
This noncomputable mathematical interface is independent of scan fuel and evaluation order.
Membership and leastness lemmas connect it to finite executable searches.
-/
noncomputable def firstStopNeOne (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) :
    ℕ := by classical exact Nat.find h

/--
The selected pure-minus-one first stop satisfies its complete stopping-set conditions.
For arbitrary `C` and `n`, nonemptiness `h` is the only premise. The proof is `Nat.find_spec h`.
This supplies an actual stopping witness when comparing rules or proving bounded search success.
-/
theorem firstStopNegOne_mem (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) :
    firstStopNegOne C n h ∈ FirstStopNegOneSet C n := by classical exact Nat.find_spec h

/--
The selected factor-detecting first stop satisfies its complete stopping-set conditions.
For arbitrary `C` and `n`, nonemptiness `h` is the only premise. The proof is `Nat.find_spec h`.
This supplies an actual stopping witness when comparing rules or proving bounded search success.
-/
theorem firstStopNeOne_mem (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) :
    firstStopNeOne C n h ∈ FirstStopNeOneSet C n := by classical exact Nat.find_spec h

/--
The least pure-minus-one first stop is no larger than any member `i` of its stopping set.
The input includes a nonemptiness proof `h` and membership `hi`; `Nat.find_min'` proves the bound.
This converts a constructed admissible candidate into a mathematical first-stop estimate.
-/
theorem firstStopNegOne_le (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNegOneSet C n).Nonempty) {i : ℕ}
    (hi : i ∈ FirstStopNegOneSet C n) : firstStopNegOne C n h ≤ i := by
  classical exact Nat.find_min' h hi

/--
The least factor-detecting first stop is no larger than any member `i` of its stopping set.
The input includes a nonemptiness proof `h` and membership `hi`; `Nat.find_min'` proves the bound.
This converts a constructed admissible candidate into a mathematical first-stop estimate.
-/
theorem firstStopNeOne_le (C : ℕ → Prop) (n : ℕ) (h : (FirstStopNeOneSet C n).Nonempty) {i : ℕ}
    (hi : i ∈ FirstStopNeOneSet C n) : firstStopNeOne C n h ≤ i := by
  classical exact Nat.find_min' h hi

/--
Every magnitude strictly below the pure-minus-one first stop lies outside its stopping set.
Assume nonemptiness and `i < firstStopNegOne C n h`. If `i` were a member, leastness would give
the contradictory reverse inequality. This excludes earlier successful candidates in
common-prefix proofs of executable scans and candidate-order comparisons.
-/
theorem not_mem_firstStopNegOneSet_of_lt (C : ℕ → Prop) (n : ℕ)
    (h : (FirstStopNegOneSet C n).Nonempty) {i : ℕ} (hi : i < firstStopNegOne C n h) :
    i ∉ FirstStopNegOneSet C n := by
  intro hmem
  exact (Nat.not_le_of_lt hi) (firstStopNegOne_le C n h hmem)

/--
Every magnitude strictly below the factor-detecting first stop lies outside its stopping set.
Assume nonemptiness and `i < firstStopNeOne C n h`. If `i` were a member, leastness would give
the contradictory reverse inequality. This excludes earlier successful candidates in
common-prefix proofs of executable scans and candidate-order comparisons.
-/
theorem not_mem_firstStopNeOneSet_of_lt (C : ℕ → Prop) (n : ℕ)
    (h : (FirstStopNeOneSet C n).Nonempty) {i : ℕ} (hi : i < firstStopNeOne C n h) :
    i ∉ FirstStopNeOneSet C n := by
  intro hmem
  exact (Nat.not_le_of_lt hi) (firstStopNeOne_le C n h hmem)

end PseudoPrime.PrimeTest
