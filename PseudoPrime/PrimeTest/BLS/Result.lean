/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Data.Nat.Prime.Basic

/-!
# Certified BLS outcomes
-/

namespace PseudoPrime.PrimeTest.BLS

/-- A bounded BLS attempt distinguishes certified prime and composite outcomes, exhausted
searches, and inputs below the primality domain. The first two constructors carry their proofs. -/
inductive BLSResult (n : ℕ) where
  /-- A proof that the original input is prime. -/
  | prime (proof : Nat.Prime n)
  /-- A proof that the original input is not prime. -/
  | composite (proof : ¬Nat.Prime n)
  /-- Neither bounded search produced a primality or compositeness proof. -/
  | unknown
  /-- The input is outside the domain `1 < n`. -/
  | invalidInput (proof : n ≤ 1)

/-- Read the correctness proposition carried by a BLS result. `unknown` is intentionally
uninformative; every conclusive or invalid-input constructor returns its corresponding proof. -/
def BLSResult.sound {n : ℕ} (result : BLSResult n) : Prop :=
  match result with
  | .prime _ => Nat.Prime n
  | .composite _ => ¬Nat.Prime n
  | .unknown => True
  | .invalidInput _ => n ≤ 1

/-- Every result constructor carries a proof of its stated correctness proposition. -/
theorem BLSResult.sound_proof {n : ℕ} (result : BLSResult n) : result.sound := by
  cases result with
  | prime proof => exact proof
  | composite proof => exact proof
  | unknown => exact True.intro
  | invalidInput proof => exact proof

end PseudoPrime.PrimeTest.BLS
