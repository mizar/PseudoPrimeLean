/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Execution.Tests.PrimalityExecution

/-! Compatibility import for declarations relocated to their namespace directories. -/

@[expose] public section

/-- Run integration regressions without exporting them from a library root. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.Execution.Tests.runTests
