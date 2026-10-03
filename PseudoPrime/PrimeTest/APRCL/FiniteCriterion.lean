/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.APRCL.PairCheck
import PseudoPrime.PrimeTest.APRCL.Criterion

/-!
# Finite APR-CL checks and the final orbit criterion

The finite pair and flag checks provide explicit checked inputs. The local
Gauss/Frobenius implication remains a separate assumption in this interface.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- A successful finite main-and-flag check feeds its actual checked evidence
to the local block implication, then the early-stop orbit scan proves primality.
The local implication must derive both the two-primary and odd auxiliary-prime
blocks from the finite evidence and exponent residues; it is not supplied by
the Bool check alone. -/
theorem prime_of_checked_localBlocks_scanLoopEarly_none {n t : ℕ}
    (entries : List (APRCLPairInput n)) (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t) (a : ℕ → ℕ → ℕ)
    (hlocal :
      (∀ p k q,
          (p, k, q) ∈ requiredPairKeys t →
            ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true) →
        (∀ p,
          Nat.Prime p →
            p ∣ t →
            ∃ evidence,
              LpEvidenceData.collect t p candidates = some evidence ∧ evidence.check t p = true) →
        ∀ ℓ,
          Nat.Prime ℓ →
            ℓ ∣ n →
            ∀ i,
              (∀ p ∈ t.primeFactors, Nat.ModEq (p ^ Nat.factorization t p) i (a ℓ p)) →
                Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
                  ∀ q ∈ (auxiliaryPrimes t).erase 2,
                    Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) : Nat.Prime n := by
  obtain ⟨ht, hmain, hflags⟩ := checkRequiredWithFlags_spec entries candidates hcheck
  have hblocks := hlocal (fun p k q hkey => (hmain p k q hkey).2) hflags
  exact prime_of_residueConditions_scanLoopEarly_none ht hn hsize a hblocks hscan

/-- A local implication phrased directly in terms of every checked required pair
and its CRT residue also feeds the final scan. This form uses the finite pair
keys without first enlarging each residue to the full prime-power factor of `t`.
The Gauss/Frobenius block implication is still an explicit assumption. -/
theorem prime_of_checked_pairBlocks_scanLoopEarly_none {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ ℓ,
        Nat.Prime ℓ →
          ℓ ∣ n →
          ∀ i,
            (∀ p k q,
                (p, k, q) ∈ requiredPairKeys t →
                  Nat.ModEq (primePowerIndex p k) i (a ℓ p) ∧
                    ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true) →
              (∀ p,
                Nat.Prime p →
                  p ∣ t →
                  ∃ evidence,
                    LpEvidenceData.collect t p candidates = some evidence ∧
                      evidence.check t p = true) →
              Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
                ∀ q ∈ (auxiliaryPrimes t).erase 2,
                  Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) : Nat.Prime n := by
  obtain ⟨ht, _, hflags⟩ := checkRequiredWithFlags_spec entries candidates hcheck
  apply prime_of_modulus_localOrbit_scanLoopEarly_none ht hn hsize
  · intro ℓ hprime hdvd
    obtain ⟨i, hit, hpairs⟩ := checkRequiredWithFlags_commonExponent entries candidates hcheck (a ℓ)
    exact ⟨i, hit, hlocal ℓ hprime hdvd i hpairs hflags⟩
  · exact hscan

/-- Record the actual source of a checked flag for every prime dividing `t`.
An odd prime may use the initial noncongruence; otherwise a candidate pair
must belong to the supplied list and pass its guard and main test. This
proposition is the finite evidence passed to the local number-theoretic kernel. -/
def checkedFlagSources {n : ℕ} (t : ℕ) (candidates : List (LpEvidenceData n)) : Prop :=
  ∀ p,
    Nat.Prime p →
      p ∣ t →
      (2 < p ∧ n ^ (p - 1) % p ^ 2 ≠ 1 ∧ (LpEvidenceData.initial : LpEvidenceData n) ∈ candidates) ∨
        ∃ input : APRCLPairInput n,
          LpEvidenceData.pair input ∈ candidates ∧
            input.key.1 = p ∧ input.check.flagConditionMet = true ∧ input.check.passed = true

/-- When two divides `t`, its flag cannot come from the odd-prime initial
condition. A checked pair in the candidate list must provide the guard. -/
theorem checkedFlagSources_two {n t : ℕ} {candidates : List (LpEvidenceData n)}
    (hsources : checkedFlagSources t candidates) (h2 : 2 ∣ t) :
    ∃ input : APRCLPairInput n,
      LpEvidenceData.pair input ∈ candidates ∧
        input.key.1 = 2 ∧ input.check.flagConditionMet = true ∧ input.check.passed = true := by
  rcases hsources 2 Nat.prime_two h2 with hin | hpair
  · exact False.elim (Nat.lt_irrefl 2 hin.1)
  · exact hpair

/-- Successful finite checking supplies the guarded pair required for the
two-primary flag whenever two divides the parameter. -/
theorem checkRequiredWithFlags_two_guard {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) (h2 : 2 ∣ t) :
    ∃ input : APRCLPairInput n,
      LpEvidenceData.pair input ∈ candidates ∧
        input.key.1 = 2 ∧ input.check.flagConditionMet = true ∧ input.check.passed = true := by
  exact
    checkedFlagSources_two (checkRequiredWithFlags_sources_in_candidates entries candidates hcheck)
      h2

/-- The final criterion can consume concrete initial-condition or guarded-pair
sources for each flag, together with the checked pair residues. The required
implication from these sources to local block congruences remains explicit. -/
theorem prime_of_checked_sourceBlocks_scanLoopEarly_none {n t : ℕ}
    (entries : List (APRCLPairInput n)) (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) (hn : 2 ≤ n)
    (hsize : n < modulus t * modulus t) (a : ℕ → ℕ → ℕ)
    (hlocal :
      ∀ ℓ,
        Nat.Prime ℓ →
          ℓ ∣ n →
          ∀ i,
            (∀ p k q,
                (p, k, q) ∈ requiredPairKeys t →
                  Nat.ModEq (primePowerIndex p k) i (a ℓ p) ∧
                    ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true) →
              checkedFlagSources t candidates →
              Nat.ModEq (2 ^ (2 + Nat.factorization t 2)) ℓ (n ^ i) ∧
                ∀ q ∈ (auxiliaryPrimes t).erase 2,
                  Nat.ModEq (q ^ (1 + Nat.factorization t q)) ℓ (n ^ i))
    (hscan : powerDivisorScanLoopEarly n (modulus t) t = none) : Nat.Prime n := by
  have hsources : checkedFlagSources t candidates :=
    checkRequiredWithFlags_sources_in_candidates entries candidates hcheck
  exact
    prime_of_checked_pairBlocks_scanLoopEarly_none entries candidates hcheck hn hsize a
      (fun ℓ hprime hdvd i hpairs _ => hlocal ℓ hprime hdvd i hpairs hsources) hscan

end PseudoPrime.PrimeTest.APRCL
