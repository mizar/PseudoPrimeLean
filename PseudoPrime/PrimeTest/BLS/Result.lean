/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Certified BLS outcomes
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/--
Proof-carrying outcome of a bounded BLS attempt at natural input `n`.
`prime` stores `Nat.Prime n`, `composite` stores its negation, `unknown` records no proof,
and `invalidInput` stores `n ≤ 1`. Exhausted witness searches are not composite certificates.
BLS generators retain the invalid-input diagnostic; projection to `Decision n` later converts
it to certified non-primality while preserving the other conclusive proofs.
-/
inductive BLSResult (n : ℕ) where
  /-- A proof that the original input is prime. -/
  | prime (proof : Nat.Prime n)
  /-- A proof that the original input is not prime. -/
  | composite (proof : ¬Nat.Prime n)
  /-- Neither bounded search produced a primality or compositeness proof. -/
  | unknown
  /-- The input is outside the domain `1 < n`. -/
  | invalidInput (proof : n ≤ 1)

/--
Correctness proposition represented by a BLS result, without extracting its proof.
Map `prime` to `Nat.Prime n`, `composite` to `¬Nat.Prime n`, `invalidInput` to `n ≤ 1`, and
`unknown` to the uninformative proposition `True`. `sound_proof` certifies this proposition
for every constructor; no primality assertion is attached to search exhaustion.
-/
def BLSResult.sound {n : ℕ} (result : BLSResult n) : Prop :=
  match result with
  | .prime _ => Nat.Prime n
  | .composite _ => ¬Nat.Prime n
  | .unknown => True
  | .invalidInput _ => n ≤ 1

/--
Every BLS result proves the correctness proposition selected by `BLSResult.sound`.
The theorem has no extra arithmetic assumptions: case analysis extracts each carried proof,
and uses `True.intro` for the inconclusive constructor. It validates the proof-carrying result
interface independently of the algorithm that produced the result.
-/
theorem BLSResult.sound_proof {n : ℕ} (result : BLSResult n) : result.sound := by
  cases result with
  | prime proof => exact proof
  | composite proof => exact proof
  | unknown => exact True.intro
  | invalidInput proof => exact proof

end PseudoPrime.PrimeTest.BLS
