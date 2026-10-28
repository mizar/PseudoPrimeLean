/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MethodDecisionTests.MethodDecisions

/-! Compatibility import for declarations relocated to their namespace directories. -/

@[expose] public section

/-- Execute individual method regressions outside the public library. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.MethodDecisionTests.runTests
