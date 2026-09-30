import PseudoPrime.PrimeTest.Result
import PseudoPrime.PrimeTest.APRCL.KnownDivisor

/-! # APR-CL adapter to certified primality decisions -/

namespace PseudoPrime.PrimeTest.APRCL

/-- Extract only proved conclusions from APR-CL execution.
Pending replay acceptance is unknown here; retain the original ExecutionResult to keep its
certificate and local-kernel obligation. This projection does not resolve that obligation. -/
def ExecutionResult.toDecision {n : ℕ} {limits : CertificateLimits} :
    ExecutionResult n limits → Decision n
  | .prime hp => .prime hp
  | .notPrime hp => .notPrime hp
  | .pending _ _ => .unknown
  | .unknown => .unknown

end PseudoPrime.PrimeTest.APRCL
