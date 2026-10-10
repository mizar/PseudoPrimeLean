/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Result
public import PseudoPrime.PrimeTest.APRCL.KnownDivisor

/-! # APR-CL adapter to certified primality decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest.APRCL

/--
Extract proved primality conclusions from APR-CL execution with certificate limits `limits`.
Preserve the `prime` and `notPrime` proof fields; map both `pending` and `unknown` to
`Decision.unknown`. A replay-accepted pending certificate still has a local-kernel obligation,
so its acceptance is not promoted to a prime proof. Staged execution uses this projection
while retaining the original APR-CL result when certificate evidence must survive.
-/
def ExecutionResult.toDecision {n : ℕ} {limits : CertificateLimits} :
    ExecutionResult n limits → Decision n
  | .prime hp => .prime hp
  | .notPrime hp => .notPrime hp
  | .pending _ _ => .unknown
  | .unknown => .unknown

end PseudoPrime.PrimeTest.APRCL
