/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.BPSW.Wheel30
import PseudoPrime.PrimeTest.BPSW.ConditionalEuler
import PseudoPrime.PrimeTest.BLS.Decision
import PseudoPrime.PrimeTest.APRCL.Decision
import PseudoPrime.PrimeTest.FactorWitness

/-!
# Staged certified execution
Keep the APR-CL pending certificate when earlier methods yield no proved decision.
Budgets belong to the caller-supplied searches; BPSW has its own search cost.
-/

namespace PseudoPrime.PrimeTest.Execution

/-- Finish on a proved decision, otherwise call the deferred next stage.
The thunk prevents evaluation of an expensive fallback after a conclusive result. -/
def continueWith {n : ℕ} {limits : APRCL.CertificateLimits} (d : Decision n)
    (next : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  match d with
  | .prime hp => .prime hp
  | .notPrime hp => .notPrime hp
  | .unknown => next ()

/-- Run a proved one-sided decision filter between small-input classification and rho/BLS/APR-CL.
The filter may include parameter guards without satisfying a global Boolean test specification.
It is deferred until the small-input stage is inconclusive; unknown continues to factor searches. -/
def runWithDecision (smallLimit n : ℕ) (filter : Unit → Decision n)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  continueWith (SmallInput.classify (max 2 smallLimit) n) fun _ ↦
    continueWith (filter ()) fun _ ↦
      continueWith (FactorWitness.decideMany n attempts) fun _ ↦
        continueWith (bls ()).toDecision aprcl

/-- Try small inputs, a specified probable-prime filter, rho, BLS, then APR-CL.
Zero, one and two are handled even with smallLimit zero. Rejection requires a proof;
acceptance of the filter and exhaustion of rho/BLS continue to the next stage.
The final result preserves APR-CL pending evidence without claiming primality. -/
def run (test : PrimalityTest) (spec : PrimalityTestSpec test) (smallLimit n : ℕ)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  runWithDecision smallLimit n (fun _ ↦ decideByTest test spec n) attempts bls aprcl

/-- Inconclusive stages preserve the exact fallback result, including pending certificates. -/
theorem continueWith_unknown {n : ℕ} {limits : APRCL.CertificateLimits}
    (next : Unit → APRCL.ExecutionResult n limits) : continueWith .unknown next = next () := by rfl

/-- Run the unconditional factor-detecting ordinary or strengthened BPSW decision.
Unknown acceptance continues to rho/BLS/APR-CL with the caller's original budgets and thunks.
The finite Selfridge stop contract certifies rejection without introducing GRH. -/
def runBPSWWheel30 (smallLimit n : ℕ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  runWithDecision smallLimit n (fun _ ↦ BPSW.decideWheel30 n strengthened) attempts bls aprcl

/-- Run staged certified execution for a signed ordinary or strengthened BPSW input.
Results and caller-supplied fallback thunks are indexed by the nonnegative interpretation.
Negative values enter the existing zero classification and cannot reach the fallbacks. -/
def runBPSWWheel30Int (smallLimit : ℕ) (z : ℤ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult z.toNat)
    (aprcl : Unit → APRCL.ExecutionResult z.toNat limits) : APRCL.ExecutionResult z.toNat limits :=
  runWithDecision smallLimit z.toNat (fun _ ↦ BPSW.decideWheel30Int z strengthened) attempts bls
    aprcl

/-- Signed execution preserves the complete natural staged result at toNat.
The equality includes budgets, factor attempts, and both fallback thunks. -/
theorem runBPSWWheel30Int_eq (smallLimit : ℕ) (z : ℤ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult z.toNat)
    (aprcl : Unit → APRCL.ExecutionResult z.toNat limits) :
    runBPSWWheel30Int smallLimit z strengthened attempts bls aprcl =
      runBPSWWheel30 smallLimit z.toNat strengthened attempts bls aprcl := by
  simp only [runBPSWWheel30Int, BPSW.decideWheel30Int_eq, runBPSWWheel30]

/-- Zero is rejected by the initial classification for every limit and fallback.
No probable-prime, factor-search, BLS, or APR-CL stage is reached. -/
theorem runWithDecision_zero (smallLimit : ℕ) (filter : Unit → Decision 0)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult 0)
    (aprcl : Unit → APRCL.ExecutionResult 0 limits) :
    runWithDecision smallLimit 0 filter attempts bls aprcl = .notPrime Nat.not_prime_zero := by
  have ht : SmallInput.isPrimeUpTo (max 2 smallLimit) 0 = some false := by
    simp only [SmallInput.isPrimeUpTo, Nat.zero_le, ↓reduceIte, Nat.reduceLeDiff, false_and,
      decide_false]
  have hc : SmallInput.classify (max 2 smallLimit) 0 = .notPrime Nat.not_prime_zero := by
    unfold SmallInput.classify
    split
    · rename_i he
      rw [ht] at he
      cases he
    · rename_i he
      rw [ht] at he
      cases he
    · rfl
  rw [runWithDecision, hc]
  rfl

/-- An input equal to zero produces a certified rejection independently of the thunks.
The zero execution theorem transports the dependent result index. -/
theorem runWithDecision_notPrime_of_zero (smallLimit n : ℕ) (hn : n = 0)
    (filter : Unit → Decision n) (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) :
    ∃ hp : ¬n.Prime, runWithDecision smallLimit n filter attempts bls aprcl = .notPrime hp := by
  subst n
  exact ⟨Nat.not_prime_zero, runWithDecision_zero smallLimit filter attempts bls aprcl⟩

/-- Negative signed inputs end in certified rejection at the small-input stage.
The result is independent of the BPSW flag, budgets, factor attempts, and fallbacks. -/
theorem runBPSWWheel30Int_negative (smallLimit : ℕ) (z : ℤ) (strengthened : Bool) (hz : z < 0)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult z.toNat)
    (aprcl : Unit → APRCL.ExecutionResult z.toNat limits) :
    ∃ hp : ¬z.toNat.Prime,
      runBPSWWheel30Int smallLimit z strengthened attempts bls aprcl = .notPrime hp := by
  exact
    runWithDecision_notPrime_of_zero smallLimit z.toNat (Int.toNat_of_nonpos (Int.le_of_lt hz)) _
      attempts bls aprcl

/-- Run staged execution with the optional conditional-Euler Wheel30 decision.
Use the caller's factor attempts, BLS thunk, and APR-CL thunk after unknown acceptance.
The new decision's all-input equality preserves all existing budgets and fallback outcomes. -/
def runBPSWWheel30ReducedEuler (smallLimit n : ℕ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  runWithDecision smallLimit n (fun _ ↦ BPSW.decideWheel30ReducedEuler n strengthened) attempts bls
    aprcl

/-- Conditional Euler omission preserves the entire natural staged execution result.
Rewrite the certified decision inside runWithDecision, including the caller's searches
and deferred fallback thunks. No performance assumption is needed for this equality. -/
theorem runBPSWWheel30ReducedEuler_eq (smallLimit n : ℕ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) :
    runBPSWWheel30ReducedEuler smallLimit n strengthened attempts bls aprcl =
      runBPSWWheel30 smallLimit n strengthened attempts bls aprcl := by
  simp only [runBPSWWheel30ReducedEuler, BPSW.decideWheel30ReducedEuler_eq, runBPSWWheel30]

/-- Signed staged execution with the optional conditional-Euler Wheel30 decision.
The result index and fallback thunks use toNat, as in the existing signed interface.
Negative inputs retain certified small-input rejection before later searches. -/
def runBPSWWheel30ReducedEulerInt (smallLimit : ℕ) (z : ℤ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult z.toNat)
    (aprcl : Unit → APRCL.ExecutionResult z.toNat limits) : APRCL.ExecutionResult z.toNat limits :=
  runWithDecision smallLimit z.toNat (fun _ ↦ BPSW.decideWheel30ReducedEulerInt z strengthened)
    attempts bls aprcl

/-- For every integer input, conditional Euler omission preserves the existing staged result.
The signed decision equality transports the result with all budgets and fallback thunks. -/
theorem runBPSWWheel30ReducedEulerInt_eq (smallLimit : ℕ) (z : ℤ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult z.toNat)
    (aprcl : Unit → APRCL.ExecutionResult z.toNat limits) :
    runBPSWWheel30ReducedEulerInt smallLimit z strengthened attempts bls aprcl =
      runBPSWWheel30Int smallLimit z strengthened attempts bls aprcl := by
  simp only [runBPSWWheel30ReducedEulerInt, BPSW.decideWheel30ReducedEulerInt_eq, runBPSWWheel30Int]

/-- Run staged execution with the common precheck before the Wheel30 BPSW filter.
Caller-supplied factor attempts and deferred BLS/APR-CL fallbacks retain their budgets. -/
def runBPSWWheel30WithPrecheck (smallLimit n : ℕ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) : APRCL.ExecutionResult n limits :=
  runWithDecision smallLimit n (fun _ ↦ BPSW.decideWheel30WithPrecheck n strengthened) attempts bls
    aprcl

/-- The precheck-first filter preserves the entire staged execution result on every input.
The certified decision equality transports both rejection and all fallback outcomes. -/
theorem runBPSWWheel30WithPrecheck_eq (smallLimit n : ℕ) (strengthened : Bool)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits} (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) :
    runBPSWWheel30WithPrecheck smallLimit n strengthened attempts bls aprcl =
      runBPSWWheel30 smallLimit n strengthened attempts bls aprcl :=
  congrArg (fun filter ↦ runWithDecision smallLimit n (fun _ ↦ filter) attempts bls aprcl)
    (BPSW.decideWheel30WithPrecheck_eq n strengthened)

end PseudoPrime.PrimeTest.Execution
