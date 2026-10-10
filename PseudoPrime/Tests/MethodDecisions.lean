/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Execution
public import PseudoPrime.PrimeTest.MillerRabin.Decision
public import PseudoPrime.PrimeTest.EulerJacobi.Decision
public import PseudoPrime.PrimeTest.Lucas.Decision
public import PseudoPrime.PrimeTest.LucasV.Decision
public import PseudoPrime.PrimeTest.StrongLucas.Decision
public import PseudoPrime.PrimeTest.BPSW.Wheel30

/-! # Individual probable-prime decision contracts -/

@[expose] public section

namespace PseudoPrime.PrimeTest.MethodDecisionTests

/-- All five requested methods plus Strong Lucas on common explicit inputs. -/
def decisions (n : ℕ) : List (PrimeTest.Decision n) :=
  [MillerRabin.decideBase2 n, MillerRabin.decideWithBase n 2, EulerJacobi.decideWithBase n 2,
    EulerJacobi.decideWithIntBase n (-1), Lucas.decideWithParams n 5 1 (-1),
    LucasV.decideWithParams n 5 1 (-1), StrongLucas.decideWithParams n 5 1 (-1),
    BPSW.decideWheel30 n false, BPSW.decideWheel30 n true]

/-- Verify boundaries, parameter guards, pseudoprimes and the downstream execution consumer. -/
def runTests : IO Unit := do
  for n in List.range 51 do
    let exactResult := PrimeTest.SmallInput.classify 50 n
    for result in decisions n do
      unless result.toOption != some true do
        throw (IO.userError "probable-prime comparison certified primality")
      if exactResult.toOption == some true then
        unless result.toOption == none do
          throw (IO.userError "prime rejected")
  unless (MillerRabin.decideWithBase 7 7).toOption == none do
    throw (IO.userError "non-coprime prime base rejected")
  unless (MillerRabin.decideBase2 2047).toOption == none do
    throw (IO.userError "strong pseudoprime promoted")
  unless (EulerJacobi.decideWithBase 561 2).toOption == none do
    throw (IO.userError "Euler-Jacobi pseudoprime promoted")
  unless (EulerJacobi.decideWithBase 9 0).toOption == none do
    throw (IO.userError "zero base comparison changed meaning")
  for method in [Lucas.decideWithParams, LucasV.decideWithParams, StrongLucas.decideWithParams] do
    unless (method 7 6 1 (-1)).toOption == none do
      throw (IO.userError "invalid discriminant used")
    unless (method 11 5 1 (-1)).toOption == none do
      throw (IO.userError "Jacobi plus-one treated as composite")
    unless (method 5 5 1 (-1)).toOption == none do
      throw (IO.userError "Jacobi zero treated as composite")
    unless (method 27 5 1 (-1)).toOption == some false do
      throw (IO.userError "supported Lucas rejection missing")
  let limits : PrimeTest.APRCL.CertificateLimits := ⟨⟨32, 4, 16, 8⟩, 12, 2⟩
  for filter in
    [fun _ : Unit ↦ Lucas.decideWithParams 27 5 1 (-1), fun _ ↦ LucasV.decideWithParams 27 5 1 (-1),
      fun _ ↦ StrongLucas.decideWithParams 27 5 1 (-1)] do
    let result :=
      Execution.runWithDecision 2 27 filter [] (fun _ ↦ .unknown) (limits := limits)
        (fun _ ↦ .unknown)
    unless result.toDecision.toOption == some false do
      throw (IO.userError "guarded filter not connected to execution")

end PseudoPrime.PrimeTest.MethodDecisionTests

/-- Execute individual method regressions outside the public library. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.MethodDecisionTests.runTests
