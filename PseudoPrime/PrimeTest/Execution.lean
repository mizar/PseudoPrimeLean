import PseudoPrime.PrimeTest.Decision
import PseudoPrime.PrimeTest.BPSW.Top
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
def continueWith {n : ℕ} {limits : APRCL.CertificateLimits}
 (d : Decision n)
 (next : Unit → APRCL.ExecutionResult n limits) :
 APRCL.ExecutionResult n limits :=
 match d with
 | .prime hp => .prime hp
 | .notPrime hp => .notPrime hp
 | .unknown => next ()
/-- Run a proved one-sided decision filter between small-input classification and rho/BLS/APR-CL.
The filter may include parameter guards without satisfying a global Boolean test specification.
It is deferred until the small-input stage is inconclusive; unknown continues to factor searches. -/
def runWithDecision (smallLimit n : ℕ)
    (filter : Unit → Decision n)
    (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
    {limits : APRCL.CertificateLimits}
    (bls : Unit → BLS.BLSResult n)
    (aprcl : Unit → APRCL.ExecutionResult n limits) :
    APRCL.ExecutionResult n limits :=
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
 {limits : APRCL.CertificateLimits}
 (bls : Unit → BLS.BLSResult n)
 (aprcl : Unit → APRCL.ExecutionResult n limits) :
 APRCL.ExecutionResult n limits :=
 runWithDecision smallLimit n (fun _ ↦ decideByTest test spec n) attempts bls aprcl
/-- Instantiate the staged entry with the proved unconditional BPSW specification.
BLS and APR-CL generators are supplied as thunks with their own explicit budgets.
This is a finite execution interface, not a polynomial-time or success guarantee. -/
def runBPSW (smallLimit n : ℕ)
 (attempts : List NumberTheory.Factorization.PollardRho.Attempt)
 {limits : APRCL.CertificateLimits}
 (bls : Unit → BLS.BLSResult n)
 (aprcl : Unit → APRCL.ExecutionResult n limits) :
 APRCL.ExecutionResult n limits :=
 run bailliePSW bailliePSW_spec_unconditional smallLimit n attempts bls aprcl
/-- Inconclusive stages preserve the exact fallback result, including pending certificates. -/
theorem continueWith_unknown {n : ℕ}
 {limits : APRCL.CertificateLimits}
 (next : Unit → APRCL.ExecutionResult n limits) :
 continueWith .unknown next = next () := by
 rfl
end PseudoPrime.PrimeTest.Execution
