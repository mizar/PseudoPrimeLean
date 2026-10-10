/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Result
public import PseudoPrime.PrimeTest.BLS.Certificate

/-! # BLS adapter to certified primality decisions -/

@[expose] public section

namespace PseudoPrime.PrimeTest.BLS

/--
Project a BLS result at `n` to the shared proof-carrying `Decision n`.
Preserve prime proofs, map composite proofs to `notPrime`, and leave exhausted searches
`unknown`. An `invalidInput` result carries an upper bound below two, which contradicts
`Nat.Prime.two_le` and therefore certifies non-primality. The projection drops the distinction
between invalid input and compositeness while the original BLS result retains that diagnostic.
-/
def BLSResult.toDecision {n : ℕ} : BLSResult n → Decision n
  | .prime hp => .prime hp
  | .composite hp => .notPrime hp
  | .unknown => .unknown
  | .invalidInput h => .notPrime (fun hp ↦ (Nat.not_succ_le_self 1) (hp.two_le.trans h))

end PseudoPrime.PrimeTest.BLS
