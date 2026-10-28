/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.APRCL.JsonTests.APRCLJson

/-! Compatibility import for declarations relocated to their namespace directories. -/

@[expose] public section

/-- Run JSON replay regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.APRCL.JsonTests.run
