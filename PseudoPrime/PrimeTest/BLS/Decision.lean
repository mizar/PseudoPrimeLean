import PseudoPrime.PrimeTest.Result
import PseudoPrime.PrimeTest.BLS.Certificate

/-! # BLS adapter to certified primality decisions -/

namespace PseudoPrime.PrimeTest.BLS

/-- Project BLS outcomes to the common proof-only interface.
Inputs below two are proved non-prime; failed searches remain unknown.
The original BLS result retains its separate invalid-input diagnostic. -/
def BLSResult.toDecision {n : ℕ} : BLSResult n → Decision n
  | .prime hp => .prime hp
  | .composite hp => .notPrime hp
  | .unknown => .unknown
  | .invalidInput h => .notPrime (fun hp ↦ (Nat.not_succ_le_self 1) (hp.two_le.trans h))

end PseudoPrime.PrimeTest.BLS
