/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Factorization.PrimePow

/-! # Sequential certificates for prime-power support -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a candidate integer `n`, witness `0` marks a candidate prime power;
its status is certified separately.
A nonzero witness certifies two coprime factors greater than one, avoiding
a primality or factorization search for that integer. -/
def primePowerWitnessCheck (n d : ℕ) : Bool :=
  if d = 0 then true else decide (1 < d ∧ n % d = 0 ∧ 1 < n / d ∧ Nat.Coprime d (n / d))

/-- Check a consecutive stream of prime-power witnesses starting at `n`.
The recursion consumes the list from its head and does not use indexed access. -/
def primePowerWitnessScan (n : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => primePowerWitnessCheck n d && primePowerWitnessScan (n + 1) ds

/-- Extract the integers marked as prime powers by zero witnesses. The output
preserves input order, and the scan soundness theorem verifies the marks. -/
def primePowerWitnessEvents (n : ℕ) : List ℕ → List ℕ
  | [] => []
  | d :: ds =>
    if d = 0 then n :: primePowerWitnessEvents (n + 1) ds else primePowerWitnessEvents (n + 1) ds

end PseudoPrime.AnalyticNumberTheory.Arithmetic
