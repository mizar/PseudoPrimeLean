/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Factorization.Defs
import PseudoPrime.PrimeTest.Result

/-! # Bounded trial-division primality decisions -/

namespace PseudoPrime.PrimeTest.SmallInput

/-- Decide primality by trial division only when n is at most limit.
Nat.minFac tests two and then odd divisors through the square-root stopping condition.
Some false includes zero and one; none means the limit was exceeded. -/
def isPrimeUpTo (limit n : ℕ) : Option Bool :=
  if n ≤ limit then some (decide (2 ≤ n ∧ Nat.minFac n = n)) else none

/-- Exact contract of the bounded prime test: the input is in range and the Boolean
agrees with Nat.Prime. The proof uses the smallest-factor characterization of primality. -/
theorem isPrimeUpTo_eq_some_iff {limit n : ℕ} {b : Bool} :
    isPrimeUpTo limit n = some b ↔ n ≤ limit ∧ (decide (Nat.Prime n) = b) := by
  simp only [isPrimeUpTo, ← Nat.prime_def_minFac]
  split
  · rename_i h
    simp only [Option.some.injEq, h, true_and]
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (h he.1)

/-- An accepted bounded prime test proves primality without an external hypothesis. -/
theorem isPrimeUpTo_true {limit n : ℕ} (h : isPrimeUpTo limit n = some true) : Nat.Prime n := by
  exact of_decide_eq_true (isPrimeUpTo_eq_some_iff.mp h).2

/-- A negative bounded prime test proves non-primality, including zero and one. -/
theorem isPrimeUpTo_false {limit n : ℕ} (h : isPrimeUpTo limit n = some false) : ¬Nat.Prime n := by
  exact of_decide_eq_false (isPrimeUpTo_eq_some_iff.mp h).2

/-- Classify an input by the bounded trial-division decision, carrying its proof.
Above the limit the result is unknown and no trial division is performed. -/
def classify (limit n : ℕ) : Decision n :=
  match h : isPrimeUpTo limit n with
  | none => .unknown
  | some true => .prime (isPrimeUpTo_true h)
  | some false => .notPrime (isPrimeUpTo_false h)

/-- Primality is inconclusive exactly above the selected input limit. -/
theorem isPrimeUpTo_eq_none_iff {limit n : ℕ} : isPrimeUpTo limit n = none ↔ ¬n ≤ limit := by
  unfold isPrimeUpTo
  split
  · rename_i h
    constructor
    · intro he
      cases he
    · intro he
      exact False.elim (he h)
  · rename_i h
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩

end PseudoPrime.PrimeTest.SmallInput
