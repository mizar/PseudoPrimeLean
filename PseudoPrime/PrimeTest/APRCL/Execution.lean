import PseudoPrime.PrimeTest.SmallInput
import PseudoPrime.PrimeTest.APRCL.Generate
/-!
# APR-CL entry with an independent small-input decision
Small inputs are decided unconditionally; larger APR-CL acceptance remains pending its local kernel.
-/
namespace PseudoPrime.PrimeTest.APRCL
/-- Execution result separating proved decisions from replay acceptance.
Prime and notPrime carry mathematical proofs. Pending carries only a replay-accepted certificate;
unknown records exhausted search. Zero and one belong to notPrime rather than composite. -/
inductive ExecutionResult (n : ℕ) (limits : CertificateLimits) where
  | prime (proof : Nat.Prime n)
  | notPrime (proof : ¬ Nat.Prime n)
  | pending (certificate : RawCertificate)
      (checked : verifyRawCertificate n limits certificate = true)
  | unknown
/-- Run only certificate generation after the caller has completed its direct decision stages.
Accepted replay remains pending and is bound to the original input. -/
def runCertificateSearch (n : ℕ) (limits : CertificateLimits)
    (budget : GenerationBudget) (parameters auxiliary : List ℕ) : ExecutionResult n limits :=
  match h : generateAutomaticCertificate n limits budget parameters auxiliary with
  | none => .unknown
  | some c => .pending c (generateAutomaticCertificate_verified h)

/-- Decide inputs up to smallLimit by the independent trial-division module.
Above that limit, construct APR-CL data and preserve acceptance as pending the local proof.
No complete factorization of a large target is used by this entry. -/
def runWithSmallInput (smallLimit n : ℕ) (limits : CertificateLimits)
    (budget : GenerationBudget) (parameters auxiliary : List ℕ) : ExecutionResult n limits :=
  match SmallInput.classify smallLimit n with
  | .prime hp => .prime hp
  | .notPrime hp => .notPrime hp
  | .unknown => runCertificateSearch n limits budget parameters auxiliary
/-- Resolve a replay-accepted pending certificate only after supplying the local kernel.
This is the consumer connecting the executable result to the existing final criterion. -/
def resolvePending {n : ℕ} {limits : CertificateLimits} (c : RawCertificate)
    (checked : verifyRawCertificate n limits c = true) (a : ℕ → ℕ → ℕ)
    (hlocal : ∀ entries, decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
      RawCertificateLocal n c.t entries a) : ExecutionResult n limits :=
  .prime (prime_of_verifyRawCertificate checked a hlocal)
/-- Reuse an already inconclusive small-input decision without repeating its computation. -/
theorem runWithSmallInput_of_unknown {smallLimit n : ℕ} (limits : CertificateLimits)
    (budget : GenerationBudget) (parameters auxiliary : List ℕ)
    (h : SmallInput.classify smallLimit n = .unknown) :
    runWithSmallInput smallLimit n limits budget parameters auxiliary =
      runCertificateSearch n limits budget parameters auxiliary := by
  simp only [runWithSmallInput, h]

end PseudoPrime.PrimeTest.APRCL
