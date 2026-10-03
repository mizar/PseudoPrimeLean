/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.APRCL.Certificate

/-!
# Bounded automatic APR-CL candidate construction

Construction and replay remain separate from the unproved local number-theoretic kernel.
-/

namespace PseudoPrime.PrimeTest.APRCL

structure GenerationBudget where
  /-- Number of root representatives starting at zero. -/
  maxRoots : ℕ
  /-- Number of supplied auxiliary candidates considered per missing flag. -/
  maxAuxiliary : ℕ

/-- Construct one required key with a bounded primitive-root search.
Check input and degree bounds before primality/root work, then recheck the generated raw row.
The scalar two-adic branch uses no primitive root and needs no root-search budget. -/
def constructRawRow (n : ℕ) (limits : PairInputLimits) (maxRoots : ℕ) (key : ℕ × ℕ × ℕ) :
    Option RawPairData := do
  let (p, k, q) := key
  let raw : RawPairData := ⟨p, k, q, 0⟩
  if ¬raw.WithinBounds n limits then
    none
  else if ¬(Nat.Prime p ∧ Nat.Prime q) then
    none
  else
    let g ←
      if p = 2 ∧ k = 0 then
        some 0
      else
        (List.range (min q maxRoots)).find? (primitiveRootCandidateTest q)
    let row : RawPairData := ⟨p, k, q, g⟩
    if (decodePairInput n limits row).isSome then
      some row
    else
      none

/-- Try an additional auxiliary prime for one missing flag.
Bound and check p,q before factorization; compute the exact zero-based valuation and root,
then keep the row only when its main test and flag guard succeed. -/
def constructExtraRow (n t p : ℕ) (limits : PairInputLimits) (maxRoots q : ℕ) :
    Option RawPairData := do
  if
      ¬(q ≤ limits.maxPrime ∧
          p ≤ limits.maxPrime ∧
          2 < q ∧ Nat.Prime p ∧ p ∣ t ∧ Nat.Prime q ∧ q ∉ auxiliaryPrimes t ∧ p ∣ q - 1) then
    none
  else
    let row ← constructRawRow n limits maxRoots (p, Nat.factorization (q - 1) p - 1, q)
    let input ← decodePairInput n limits row
    if input.check.flagConditionMet then
      some row
    else
      none

/-- Construct all required rows and search only for missing flags.
The caller supplies t and auxiliary-prime proposals. Bounds precede expensive construction;
each missing flag takes the first successful extra row in the permitted prefix.
No arithmetic failure is classified as compositeness. -/
def constructCandidate (n t : ℕ) (limits : CertificateLimits) (budget : GenerationBudget)
    (auxiliary : List ℕ) : Option CertificateCandidate := do
  if ¬(2 ≤ n ∧ n % 2 = 1 ∧ 0 < t ∧ Even t ∧ t ≤ limits.maxT) then
    none
  else if ¬(n < modulus t * modulus t ∧ Nat.Coprime n (t * modulus t)) then
    none
  else
    let keys := requiredPairKeys t
    if keys.length > limits.pairs.maxPairs then
      none
    else
      let main ← keys.mapM (constructRawRow n limits.pairs budget.maxRoots)
      let entries ← decodePairInputs n limits.pairs main
      if ¬entries.all (fun input ↦ input.check.passed) then
        none
      else
        let missing :=
          (requiredFlagPrimes t).filter
            (fun p ↦ (LpEvidenceData.collect t p (pairFlagCandidates entries)).isNone)
        if main.length + missing.length > limits.pairs.maxPairs then
          none
        else
          let extra ←
            missing.mapM
                (fun p ↦
                  (auxiliary.take budget.maxAuxiliary).findSome?
                    (constructExtraRow n t p limits.pairs budget.maxRoots))
          some ⟨t, main, extra⟩

/-- Bind one constructed proposal to n and replay all certificate conditions.
Only replay-accepted data can leave this per-parameter entry point. -/
def constructVerifiedCertificate (n t : ℕ) (limits : CertificateLimits) (budget : GenerationBudget)
    (auxiliary : List ℕ) : Option RawCertificate :=
  ((constructCandidate n t limits budget auxiliary).map (CertificateCandidate.bind n)).filter
    (verifyRawCertificate n limits)

/-- Search the bounded parameter prefix, stopping at the first replay-accepted certificate.
Generate keys, roots and missing-flag witnesses automatically from the supplied parameters
and auxiliary candidates. No construction is performed for later parameters after success. -/
def generateAutomaticCertificate (n : ℕ) (limits : CertificateLimits) (budget : GenerationBudget)
    (parameters auxiliary : List ℕ) : Option RawCertificate :=
  (parameters.take limits.maxCandidates).findSome?
    (fun t ↦ constructVerifiedCertificate n t limits budget auxiliary)

/-- Automatic generation always returns a certificate accepted by complete replay.
Extract the successful parameter and consume the replay filter. -/
theorem generateAutomaticCertificate_verified {n : ℕ} {limits : CertificateLimits}
    {budget : GenerationBudget} {parameters auxiliary : List ℕ} {c : RawCertificate}
    (h : generateAutomaticCertificate n limits budget parameters auxiliary = some c) :
    verifyRawCertificate n limits c = true := by
  obtain ⟨t, _, ht⟩ := List.exists_of_findSome?_eq_some h
  exact (Option.filter_eq_some_iff.mp ht).2

/-- Automatic generation feeds the final criterion under the explicit local kernel.
This theorem does not discharge RawCertificateLocal. -/
theorem generateAutomaticCertificate_prime {n : ℕ} {limits : CertificateLimits}
    {budget : GenerationBudget} {parameters auxiliary : List ℕ} {c : RawCertificate}
    (h : generateAutomaticCertificate n limits budget parameters auxiliary = some c) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ entries,
        decodePairInputs n limits.pairs (c.main ++ c.extra) = some entries →
          RawCertificateLocal n c.t entries a) :
    Nat.Prime n := by
  exact prime_of_verifyRawCertificate (generateAutomaticCertificate_verified h) a hlocal

/-- No result means that every parameter in the allowed prefix failed construction or replay.
This makes no claim about compositeness or the sufficiency of the supplied search budgets. -/
theorem generateAutomaticCertificate_none_iff {n : ℕ} {limits : CertificateLimits}
    {budget : GenerationBudget} {parameters auxiliary : List ℕ} :
    generateAutomaticCertificate n limits budget parameters auxiliary = none ↔
      ∀ t ∈ parameters.take limits.maxCandidates,
        constructVerifiedCertificate n t limits budget auxiliary = none := by
  exact List.findSome?_eq_none_iff

end PseudoPrime.PrimeTest.APRCL
