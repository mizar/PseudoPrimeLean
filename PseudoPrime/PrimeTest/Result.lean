/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import Mathlib.Data.Nat.Prime.Basic

/-!
# Certified primality decisions
This foundational interface is shared by trial division, certificate methods and test adapters.
-/

namespace PseudoPrime.PrimeTest

/-- A proved prime or non-prime conclusion, or no conclusion.
The proof fields certify the input n; notPrime includes zero and one.
Search exhaustion and probable-prime acceptance both yield unknown at this proof-only interface. -/
inductive Decision (n : ℕ) where
  | unknown
  | prime (proof : Nat.Prime n)
  | notPrime (proof : ¬Nat.Prime n)

/-- Forget proof terms for display and regression: none is inconclusive,
some true certifies primality, and some false certifies non-primality. -/
def Decision.toOption {n : ℕ} : Decision n → Option Bool
  | .unknown => none
  | .prime _ => some true
  | .notPrime _ => some false

/-- Two conclusive decisions on the same input agree, irrespective of their algorithm.
Opposite results would contradict the carried proofs; unknown provides no conclusion. -/
theorem Decision.agrees {n : ℕ} (a b : Decision n) {x y : Bool} (ha : a.toOption = some x)
    (hb : b.toOption = some y) : x = y := by
  cases a <;> cases b <;> simp only [toOption, Option.some.injEq] at ha hb
  all_goals
    first
    | contradiction
    | exact ha.symm.trans hb

end PseudoPrime.PrimeTest
