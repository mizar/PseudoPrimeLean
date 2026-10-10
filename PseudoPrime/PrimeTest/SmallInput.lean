/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.Defs
public import PseudoPrime.PrimeTest.Result

/-! # Bounded trial-division primality decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest.SmallInput

/--
Exact optional primality test with natural upper limit `limit` and input `n`.
When `n ≤ limit`, return the Boolean decision of `2 ≤ n ∧ Nat.minFac n = n`; otherwise
return `none` without evaluating trial division. The smallest-factor characterization handles
zero and one as negative results. `classify` attaches primality or non-primality proofs.
-/
def isPrimeUpTo (limit n : ℕ) : Option Bool :=
  if n ≤ limit then some (decide (2 ≤ n ∧ Nat.minFac n = n)) else none

/--
Characterize every returned Boolean `b` of the bounded small-input test.
`isPrimeUpTo limit n = some b` holds exactly when `n ≤ limit` and `decide (Nat.Prime n) = b`.
The proof rewrites the smallest-factor criterion to primality and splits the input-limit branch.
The true and false soundness lemmas extract the second conjunct of this equivalence.
-/
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

/--
An explicit `some true` from the bounded small-input test certifies `Nat.Prime n`.
The premise already guarantees that `n` is within the supplied limit. Extract the exact Boolean
primality decision from `isPrimeUpTo_eq_some_iff` and use `of_decide_eq_true`.
This proof is stored by the positive branch of `classify`.
-/
theorem isPrimeUpTo_true {limit n : ℕ} (h : isPrimeUpTo limit n = some true) : Nat.Prime n := by
  exact of_decide_eq_true (isPrimeUpTo_eq_some_iff.mp h).2

/--
An explicit `some false` from the bounded small-input test certifies `¬Nat.Prime n`.
No lower bound on `n` is required, so zero and one are included. Extract the Boolean
primality decision from the exact contract and use `of_decide_eq_false`.
This proof is stored by the negative branch of `classify`.
-/
theorem isPrimeUpTo_false {limit n : ℕ} (h : isPrimeUpTo limit n = some false) : ¬Nat.Prime n := by
  exact of_decide_eq_false (isPrimeUpTo_eq_some_iff.mp h).2

/--
Proof-carrying bounded trial-division classification of `n` with input limit `limit`.
Match `isPrimeUpTo limit n`: `none` becomes `unknown`, and the two explicit Boolean results
become `prime` or `notPrime` using their soundness lemmas. The limit bounds the input value,
not the number of trial-division iterations. Staged execution uses this exact initial stage.
-/
def classify (limit n : ℕ) : Decision n :=
  match h : isPrimeUpTo limit n with
  | none => .unknown
  | some true => .prime (isPrimeUpTo_true h)
  | some false => .notPrime (isPrimeUpTo_false h)

/--
The bounded test is inconclusive precisely when the natural input exceeds its limit.
The conclusion equates `isPrimeUpTo limit n = none` with `¬n ≤ limit`.
The proof unfolds the conditional and excludes equality of `some` with `none` in the in-range
branch. This identifies budget refusal rather than algorithmic failure or compositeness.
-/
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
