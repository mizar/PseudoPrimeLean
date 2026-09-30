import PseudoPrime.NumberTheory.Factorization.SmallInput
import PseudoPrime.PrimeTest.APRCL.Execution

/-!
# Independent small-input arithmetic regressions
Compare primality against enumeration of all proper divisors and replay returned factors.
-/

namespace PseudoPrime.PrimeTest.SmallInput.Tests

/-- An independent exhaustive divisor reference, used only for small regression inputs. -/
def referencePrime (n : ℕ) : Bool :=
  decide (2 ≤ n) && !(List.range n).any (fun d ↦ decide (2 ≤ d ∧ d ∣ n))

/-- Run small-input arithmetic and APR-CL dispatch regressions. -/
def run : IO Unit := do
  for n in List.range 501 do
    unless isPrimeUpTo 500 n == some (referencePrime n) do
      throw (IO.userError s!"primality mismatch: {n}")
    if n == 0 then
      unless (NumberTheory.Factorization.SmallInput.factorUpTo 500 n).isNone do
        throw (IO.userError "zero factorization accepted")
    else
      let some factors := NumberTheory.Factorization.SmallInput.factorUpTo 500 n
        | throw (IO.userError s!"factorization missing: {n}")
      unless factors.prod == n && factors.all referencePrime do
        throw (IO.userError s!"invalid factorization: {n}")
  unless NumberTheory.Factorization.SmallInput.factorUpTo 360 360 == some [2, 2, 2, 3, 3, 5] do
    throw (IO.userError "multiplicity mismatch")
  unless NumberTheory.Factorization.SmallInput.factorUpTo 1 1 == some [] do
    throw (IO.userError "one boundary mismatch")
  unless NumberTheory.Factorization.SmallInput.factorUpTo 49 49 == some [7, 7] do
    throw (IO.userError "square boundary mismatch")
  for n in [501, 100000000000000000000000000000000000001] do
    unless
      (NumberTheory.Factorization.SmallInput.factorUpTo 500 n).isNone &&
        (isPrimeUpTo 500 n).isNone do
      throw (IO.userError "input cap ignored")
  let limits : PseudoPrime.PrimeTest.APRCL.CertificateLimits := ⟨⟨32, 4, 16, 8⟩, 2, 1⟩
  for n in [2, 3, 5, 7, 13] do
    match PseudoPrime.PrimeTest.APRCL.runWithSmallInput 13 n limits ⟨0, 0⟩ [] [] with
    | .prime _ =>
      pure ()
    | _ =>
      throw (IO.userError "small prime did not bypass APR-CL search")
  for n in [0, 1, 4, 9, 12] do
    match PseudoPrime.PrimeTest.APRCL.runWithSmallInput 13 n limits ⟨0, 0⟩ [] [] with
    | .notPrime _ =>
      pure ()
    | _ =>
      throw (IO.userError "small nonprime was not decided")
  match PseudoPrime.PrimeTest.APRCL.runWithSmallInput 3 13 limits ⟨32, 2⟩ [2] [3, 7] with
  | .pending c _ =>
    unless PseudoPrime.PrimeTest.APRCL.verifyRawCertificate 13 limits c do
      throw (IO.userError "pending certificate failed replay")
  | _ =>
    throw (IO.userError "large input bypassed pending local kernel")
  match PseudoPrime.PrimeTest.APRCL.runWithSmallInput 3 13 limits ⟨0, 0⟩ [] [] with
  | .unknown =>
    pure ()
  | _ =>
    throw (IO.userError "exhausted search incorrectly decided input")

end PseudoPrime.PrimeTest.SmallInput.Tests

/-- Execute bounded arithmetic and dispatch regressions. -/
def main : IO Unit :=
  PseudoPrime.PrimeTest.SmallInput.Tests.run
