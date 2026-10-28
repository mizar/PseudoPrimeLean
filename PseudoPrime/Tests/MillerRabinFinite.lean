/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.FiniteTests.MillerRabinFinite

/-! Compatibility import for declarations relocated to their namespace directories. -/

@[expose] public section

/-- Execute finite two-base regressions without exporting them. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.MillerRabin.FiniteTests.runTests
