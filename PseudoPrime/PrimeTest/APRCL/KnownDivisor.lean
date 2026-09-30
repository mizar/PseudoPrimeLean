import PseudoPrime.PrimeTest.APRCL.Execution

/-!
# Direct decisions from known APR-CL prime divisors

Parameter and auxiliary hints are rechecked before being used as mathematical evidence.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- Collect divisors already suggested by bounded APR-CL parameters and auxiliary proposals.
Only positive even parameters below maxT are factored; candidate prefixes are bounded.
These are hints and are independently prime-checked before use. -/
def knownDivisorCandidates (limits : CertificateLimits) (budget : GenerationBudget)
    (parameters auxiliary : List ℕ) : List ℕ :=
  (parameters.take limits.maxCandidates).flatMap
      (fun t ↦
        if 0 < t ∧ Even t ∧ t ≤ limits.maxT then requiredFlagPrimes t ++ auxiliaryPrimeSearch t
        else []) ++
    auxiliary.take budget.maxAuxiliary

/-- Find the first in-range prime candidate dividing n; test its bound before primality.
Failure is inconclusive and does not mean that n has no prime factors. -/
def findKnownPrimeDivisor (n maxPrime : ℕ) (candidates : List ℕ) : Option ℕ :=
  candidates.find? (fun p ↦ decide (p ≤ maxPrime ∧ Nat.Prime p ∧ p ∣ n))

/-- A found divisor belongs to the supplied list, is within the bound, prime, and divides n. -/
theorem findKnownPrimeDivisor_spec {n maxPrime p : ℕ} {candidates : List ℕ}
    (h : findKnownPrimeDivisor n maxPrime candidates = some p) :
    p ∈ candidates ∧ p ≤ maxPrime ∧ Nat.Prime p ∧ p ∣ n := by
  have ht : decide (p ≤ maxPrime ∧ Nat.Prime p ∧ p ∣ n) = true :=
    List.find?_some (p := fun q ↦ decide (q ≤ maxPrime ∧ Nat.Prime q ∧ q ∣ n)) h
  exact ⟨List.mem_of_find?_eq_some h, of_decide_eq_true ht⟩

/-- A prime divisor different from n refutes primality of n.
The prime-divisor characterization closes the proof without a size or local-kernel assumption. -/
theorem not_prime_of_prime_divisor_ne {n p : ℕ} (hp : Nat.Prime p) (hd : p ∣ n) (hne : p ≠ n) :
    ¬Nat.Prime n := by
  intro hn
  exact hne ((Nat.prime_dvd_prime_iff_eq hp hn).mp hd)

/-- Decide n using a certified prime divisor: equality proves primality,
otherwise the divisor refutes primality. No APR-CL local implication is needed. -/
def resultOfKnownPrimeDivisor {n : ℕ} {limits : CertificateLimits} (p : ℕ) (hp : Nat.Prime p)
    (hd : p ∣ n) : ExecutionResult n limits :=
  if he : p = n then .prime (he ▸ hp) else .notPrime (not_prime_of_prime_divisor_ne hp hd he)

/-- Run small-input classification, then known-divisor detection, then general APR-CL search.
This detects known prime targets and composite targets beyond smallLimit before Jacobi work.
If both direct paths fail, preserve the existing pending/unknown result semantics. -/
def runWithKnownDivisors (smallLimit n : ℕ) (limits : CertificateLimits) (budget : GenerationBudget)
    (parameters auxiliary : List ℕ) : ExecutionResult n limits :=
  match SmallInput.classify smallLimit n with
  | .prime hp => .prime hp
  | .notPrime hp => .notPrime hp
  | .unknown =>
    match h :
      findKnownPrimeDivisor n limits.pairs.maxPrime
        (knownDivisorCandidates limits budget parameters auxiliary) with
    | some p =>
      let hs := findKnownPrimeDivisor_spec h
      resultOfKnownPrimeDivisor p hs.2.2.1 hs.2.2.2
    | none => runCertificateSearch n limits budget parameters auxiliary

/-- Failure excludes only in-range prime divisors from the supplied finite candidate list. -/
theorem findKnownPrimeDivisor_none_iff {n maxPrime : ℕ} {candidates : List ℕ} :
    findKnownPrimeDivisor n maxPrime candidates = none ↔
      ∀ p ∈ candidates, ¬(p ≤ maxPrime ∧ Nat.Prime p ∧ p ∣ n) := by
  unfold findKnownPrimeDivisor
  rw [List.find?_eq_none]
  simp only [decide_eq_true_eq]

end PseudoPrime.PrimeTest.APRCL
