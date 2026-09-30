/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.APRCL.RawInput

/-!
# Raw APR-CL certificate replay and finite generation

Replay uses a fixed modulus and does not discharge the local Gauss/Frobenius kernel.
-/

namespace PseudoPrime.PrimeTest.APRCL

structure RawCertificate where
  /-- Claimed target number, checked against the caller input. -/
  n : ℕ
  /-- Positive even parameter fixing the modulus. -/
  t : ℕ
  /-- Rows for keys required by the fixed parameter. -/
  main : List RawPairData
  /-- Additional guarded flag witnesses outside the fixed auxiliary set. -/
  extra : List RawPairData

structure CertificateLimits where
  /-- Limits for each pair and the combined row count. -/
  pairs : PairInputLimits
  /-- Maximum parameter before modulus construction. -/
  maxT : ℕ
  /-- Maximum number of supplied proposals considered. -/
  maxCandidates : ℕ

/-- Replay extra witnesses without enlarging the fixed modulus.
Require distinct prime indices dividing t, auxiliary primes outside its original set,
and successful guarded pair checks. Callers bound the total row count before this check. -/
def checkExtraRows (n t : ℕ) (limits : PairInputLimits) (rows : List RawPairData) : Bool :=
  decide ((rows.map (fun r ↦ r.p)).Nodup) &&
    rows.all
      (fun r ↦
        decide (Nat.Prime r.p ∧ r.p ∣ t ∧ r.q ∉ auxiliaryPrimes t) &&
          match decodePairInput n limits r with
          | none => false
          | some input => input.check.flagConditionMet)

/-- Replay a target-bound certificate under explicit limits.
Check row roles, coprimality, required pairs, all flags and the final scan with modulus t.
True records finite acceptance only; primality still requires the local mathematical kernel.
Small primes dividing the parameter modulus need a separate direct-prime path. -/
def verifyRawCertificate (n : ℕ) (limits : CertificateLimits) (c : RawCertificate) : Bool :=
  if
      c.n = n ∧
        2 ≤ n ∧
        n % 2 = 1 ∧
        0 < c.t ∧
        Even c.t ∧ c.t ≤ limits.maxT ∧ c.main.length + c.extra.length ≤ limits.pairs.maxPairs then
    if n < modulus c.t * modulus c.t ∧ Nat.Coprime n (c.t * modulus c.t) then
      decide (∀ r ∈ c.main, (r.p, r.k, r.q) ∈ requiredPairKeys c.t) &&
        checkExtraRows n c.t limits.pairs c.extra &&
        checkRawPairs n c.t limits.pairs limits.maxT (c.main ++ c.extra) &&
        decide (powerDivisorScanLoopEarly n (modulus c.t) c.t = none)
    else false
  else false

/-- Extract target agreement, size, finite checks and the fixed-modulus scan from acceptance.
The proof separates the Boolean guards for the conditional primality consumer. -/
theorem verifyRawCertificate_spec {n : ℕ} {limits : CertificateLimits} {c : RawCertificate}
    (h : verifyRawCertificate n limits c = true) :
    c.n = n ∧
      2 ≤ n ∧
      n < modulus c.t * modulus c.t ∧
      checkRawPairs n c.t limits.pairs limits.maxT (c.main ++ c.extra) = true ∧
      powerDivisorScanLoopEarly n (modulus c.t) c.t = none := by
  unfold verifyRawCertificate at h
  split at h
  · rename_i hguard
    split at h
    · rename_i harith
      have hb := Bool.and_eq_true_iff.mp h
      exact
        ⟨hguard.1, hguard.2.1, harith.1, (Bool.and_eq_true_iff.mp hb.1).2, of_decide_eq_true hb.2⟩
    · exact Bool.noConfusion h
  · exact Bool.noConfusion h

/-- The remaining local mathematical obligation for decoded rows.
It must derive the actual modulus blocks from checked residues and flag sources. -/
abbrev RawCertificateLocal (n t : ℕ) (entries : List (APRCLPairInput n)) (a : ℕ → ℕ → ℕ) : Prop :=
  ∀ ℓ,
    Nat.Prime ℓ →
      ℓ ∣ n →
      ∀ i,
        (∀ p k q,
            (p, k, q) ∈ requiredPairKeys t →
              Nat.ModEq (primePowerIndex p k) i (a ℓ p) ∧
                ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true) →
          checkedFlagSources t (pairFlagCandidates entries) →
          Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
            ∀ q ∈ (auxiliaryPrimes t).erase 2, Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i)

/-- Accepted replay implies primality when the local block implication is supplied.
Decode the checked rows and apply the existing source-block criterion; no local implication
is inferred from the Boolean checks themselves. -/
theorem prime_of_verifyRawCertificate {n : ℕ} {limits : CertificateLimits} {c : RawCertificate}
    (h : verifyRawCertificate n limits c = true) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ entries,
        decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
          RawCertificateLocal n c.t entries a) :
    Nat.Prime n := by
  obtain ⟨_, hn, hsize, hpairs, hscan⟩ := verifyRawCertificate_spec h
  obtain ⟨entries, hd, hc, _⟩ := checkRawPairs_sources hpairs
  exact
    prime_of_checked_sourceBlocks_scanLoopEarly_none entries (pairFlagCandidates entries) hc hn
      hsize a (hlocal entries hd) hscan

structure CertificateCandidate where
  /-- Positive even parameter fixing the modulus. -/
  t : ℕ
  /-- Rows for keys required by the fixed parameter. -/
  main : List RawPairData
  /-- Additional guarded flag witnesses outside the fixed auxiliary set. -/
  extra : List RawPairData

/-- Bind a proposal to the caller's input, preserving its fixed parameter and rows. -/
def CertificateCandidate.bind (n : ℕ) (candidate : CertificateCandidate) : RawCertificate :=
  ⟨n, candidate.t, candidate.main, candidate.extra⟩

/-- Return the first replay-accepted proposal in a bounded supplied prefix.
This enumerates explicit proposals, not all primes or primitive roots. None means no verified
proposal in that prefix and never certifies compositeness. -/
def generateRawCertificate (n : ℕ) (limits : CertificateLimits)
    (candidates : List CertificateCandidate) : Option RawCertificate :=
  ((candidates.take limits.maxCandidates).map (CertificateCandidate.bind n)).find?
    (verifyRawCertificate n limits)

/-- Every generated certificate passes full replay for the requested target and limits. -/
theorem generateRawCertificate_verified {n : ℕ} {limits : CertificateLimits}
    {candidates : List CertificateCandidate} {c : RawCertificate}
    (h : generateRawCertificate n limits candidates = some c) :
    verifyRawCertificate n limits c = true := by exact List.find?_some h

/-- Finite generation feeds the conditional primality consumer with the same local kernel. -/
theorem generateRawCertificate_prime {n : ℕ} {limits : CertificateLimits}
    {candidates : List CertificateCandidate} {c : RawCertificate}
    (h : generateRawCertificate n limits candidates = some c) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ entries,
        decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
          RawCertificateLocal n c.t entries a) :
    Nat.Prime n := by
  exact prime_of_verifyRawCertificate (generateRawCertificate_verified h) a hlocal

/-- Extra acceptance preserves distinct indices, exclusion from the fixed auxiliary set,
and actual decoded flag witnesses. The proof unfolds Boolean list acceptance row by row. -/
theorem checkExtraRows_spec {n t : ℕ} {limits : PairInputLimits} {rows : List RawPairData}
    (h : checkExtraRows n t limits rows = true) :
    (rows.map (fun r ↦ r.p)).Nodup ∧
      ∀ r ∈ rows,
        Nat.Prime r.p ∧
          r.p ∣ t ∧
          r.q ∉ auxiliaryPrimes t ∧
          ∃ input,
            decodePairInput n limits r = some input ∧ input.check.flagConditionMet = true := by
  obtain ⟨hunique, hall⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨of_decide_eq_true hunique, ?_⟩
  intro r hr
  obtain ⟨hshape, hflag⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp hall r hr)
  obtain ⟨hp, hd, hq⟩ := of_decide_eq_true hshape
  cases he : decodePairInput n limits r with
  | none => simp only [he, Bool.false_eq_true] at hflag
  | some input => exact ⟨hp, hd, hq, input, rfl, by simpa only [he] using hflag⟩

/-- Failure means exactly that no proposal in the bounded prefix passes replay.
The equivalence imposes no assertion about primality or proposals outside the prefix. -/
theorem generateRawCertificate_none_iff {n : ℕ} {limits : CertificateLimits}
    {candidates : List CertificateCandidate} :
    generateRawCertificate n limits candidates = none ↔
      ∀ candidate ∈ candidates.take limits.maxCandidates,
        ¬verifyRawCertificate n limits (candidate.bind n) = true := by
  unfold generateRawCertificate
  rw [List.find?_eq_none]
  constructor
  · intro h candidate hm
    exact h (candidate.bind n) (List.mem_map.mpr ⟨candidate, hm, rfl⟩)
  · intro h c hm
    obtain ⟨candidate, hmem, rfl⟩ := List.mem_map.mp hm
    exact h candidate hmem

end PseudoPrime.PrimeTest.APRCL
