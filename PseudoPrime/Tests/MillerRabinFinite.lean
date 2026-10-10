/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Finite
public import PseudoPrime.PrimeTest.Execution

/-! # Finite two-base Miller-Rabin decisions and integration regressions -/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.FiniteTests

/-- Check the complete certified range, strict cutoff and the prime-producing consumer. -/
def runTests : IO Unit := do
  for n in List.range 3000 do
    unless (decideBasesTwoThree n).toOption == (PrimeTest.SmallInput.classify 2999 n).toOption do
      throw (IO.userError s!"two-base finite classification mismatch at {n}")
  unless strongMillerRabinWithBase 2047 2 do
    throw (IO.userError "base-two exception no longer exercised")
  unless !strongMillerRabinWithBase 2047 3 do
    throw (IO.userError "base three failed to reject the exception")
  for n in [3000, 3001, 100000000000000000000000000000000000000000000000001] do
    unless (decideBasesTwoThree n).toOption == none do
      throw (IO.userError "finite certificate extrapolated")
  let limits : PrimeTest.APRCL.CertificateLimits := ⟨⟨0, 0, 0, 0⟩, 0, 0⟩
  for n in [0, 1, 2, 3, 5, 9, 2047, 2999] do
    let result :=
      Execution.runWithDecision 0 n (fun _ ↦ decideBasesTwoThree n) [] (fun _ ↦ .unknown) (limits :=
        limits) (fun _ ↦ .unknown)
    unless result.toDecision.toOption == (PrimeTest.SmallInput.classify 2999 n).toOption do
      throw (IO.userError "two-base decision lost at consumer")
  let outside :=
    Execution.runWithDecision 0 3001 (fun _ ↦ decideBasesTwoThree 3001) [] (fun _ ↦ .unknown)
      (limits := limits) (fun _ ↦ .unknown)
  unless outside.toDecision.toOption == none do
    throw (IO.userError "outside-range fallback changed meaning")

end PseudoPrime.PrimeTest.MillerRabin.FiniteTests

/-- Execute finite two-base regressions without exporting them. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.MillerRabin.FiniteTests.runTests
