import PseudoPrime.PrimeTest.APRCL.KnownDivisor

/-!
# Direct known-divisor regressions
Check decisions beyond the small-input cap and preserve inconclusive fallbacks.
-/

namespace PseudoPrime.PrimeTest.APRCL.KnownDivisorTests

/-- Bounds for parameter and auxiliary candidate construction. -/
def limits : CertificateLimits :=
  ⟨⟨32, 4, 16, 8⟩, 12, 2⟩

/-- Exercise equality, proper divisors, invalid hints and bounded fallback paths. -/
def run : IO Unit := do
  unless findKnownPrimeDivisor 49 32 [0, 1, 4, 7] == some 7 do
    throw (IO.userError "invalid candidates prevented prime divisor discovery")
  unless (findKnownPrimeDivisor 49 6 [7]).isNone do
    throw (IO.userError "prime cap ignored")
  for n in [5, 7] do
    match runWithKnownDivisors 3 n limits ⟨0, 0⟩ [4, 6] [] with
    | .prime _ =>
      pure ()
    | _ =>
      throw (IO.userError "known parameter prime not recognized")
  for n in [35, 49, 7 * (10 ^ 60 + 1)] do
    match runWithKnownDivisors 3 n limits ⟨0, 0⟩ [4, 6] [] with
    | .notPrime _ =>
      pure ()
    | _ =>
      throw (IO.userError "proper parameter divisor not recognized")
  match runWithKnownDivisors 3 17 limits ⟨0, 1⟩ [] [17] with
  | .prime _ =>
    pure ()
  | _ =>
    throw (IO.userError "explicit known prime not recognized")
  match runWithKnownDivisors 3 17 limits ⟨0, 0⟩ [] [17] with
  | .unknown =>
    pure ()
  | _ =>
    throw (IO.userError "auxiliary prefix ignored")
  match runWithKnownDivisors 3 5 { limits with maxCandidates := 0 } ⟨0, 0⟩ [4] [] with
  | .unknown =>
    pure ()
  | _ =>
    throw (IO.userError "parameter prefix ignored")
  match runWithKnownDivisors 3 13 limits ⟨32, 2⟩ [2] [3, 7] with
  | .pending c _ =>
    unless verifyRawCertificate 13 limits c do
      throw (IO.userError "fallback replay failed")
  | _ =>
    throw (IO.userError "fallback incorrectly decided prime")
  unless (knownDivisorCandidates limits ⟨0, 0⟩ [0, 1000000000] []).isEmpty do
    throw (IO.userError "invalid parameter enumerated")

end PseudoPrime.PrimeTest.APRCL.KnownDivisorTests

/-- Run direct known-divisor regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.APRCL.KnownDivisorTests.run
