/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.APRCL.FiniteCriterion

/-!
# Bounded raw APR-CL pair inputs

Executable guards construct the proof-carrying Jacobi inputs used by the four branch checks.
The local Gauss/Frobenius implication is not supplied by these constructors.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- Construct Jacobi data from executable primality and primitive-root checks.
The finite field, unit generator, exact valuation and fixed character exponents are preserved. -/
def datumFromCheckedRoot {p k q g : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hperiod : primePowerIndex p k ∣ q - 1) (hnext : ¬primePowerIndex p (k + 1) ∣ q - 1)
    (hcop : Nat.Coprime g q) (hroot : primitiveRootCandidateTest q g = true) (a b : ℕ) :
    APRCLJacobiDatumWithParameters p k a b := by
  letI : NeZero q := ⟨hq.ne_zero⟩
  refine
    ⟨hp,
      ⟨q, hq, inferInstance, (Set.finite_Ioo 0 (q - 1)).to_subtype, ZMod.unitOfCoprime g hcop, ?_,
        a, b, 1, hperiod⟩,
      rfl, rfl, hnext⟩
  apply IsPrimitiveRoot.coe_units_iff.mp
  rw [ZMod.coe_unitOfCoprime]
  exact (primitiveRootCandidateTest_eq_true_iff hq).mp hroot

/-- Build all three high two-adic Jacobi data with one auxiliary prime and generator.
The shared-generator invariants hold by construction, including the correction factor. -/
def highDataFromCheckedRoot {k q g : ℕ} (hq : Nat.Prime q) (hperiod : primePowerIndex 2 k ∣ q - 1)
    (hnext : ¬primePowerIndex 2 (k + 1) ∣ q - 1) (hcop : Nat.Coprime g q)
    (hroot : primitiveRootCandidateTest q g = true) : APRCLTwoAdicHighBranchData k
    where
  auxiliaryPrime := q
  datum₁₁ := datumFromCheckedRoot (by decide) hq hperiod hnext hcop hroot 1 1
  datum₂₁ := datumFromCheckedRoot (by decide) hq hperiod hnext hcop hroot 2 1
  datum₂ :=
    datumFromCheckedRoot (by decide) hq hperiod hnext hcop hroot (2 ^ (k - 2)) (3 * 2 ^ (k - 2))
  datum₁₁_q_eq := rfl
  datum₂₁_q_eq := rfl
  datum₂_q_eq := rfl
  datum₂₁_generator_eq := HEq.rfl
  datum₂_generator_eq := HEq.rfl

/-- Untrusted integer input for one APR-CL pair.
The index k is zero-based: the root period is p^(k+1). The generator is unused for k=0,p=2.
All mathematical admissibility conditions are rechecked before constructing typed data. -/
structure RawPairData where
  /-- Cyclotomic index prime. -/
  p : ℕ
  /-- Zero-based power index. -/
  k : ℕ
  /-- Auxiliary prime. -/
  q : ℕ
  /-- Natural representative of the proposed primitive root. -/
  generator : ℕ
  deriving Repr

/-- Bounds checked before constructing typed pairs or coefficient arrays.
maxPrime bounds p and q, maxIndex bounds k, maxDegree bounds the cyclotomic degree,
and maxPairs bounds the number of supplied rows. These are not total-time guarantees. -/
structure PairInputLimits where
  /-- Largest allowed prime parameter. -/
  maxPrime : ℕ
  /-- Largest zero-based power index. -/
  maxIndex : ℕ
  /-- Largest coefficient-array degree. -/
  maxDegree : ℕ
  /-- Largest raw input list length. -/
  maxPairs : ℕ
  deriving Repr

/-- Dispatch checked primitive-root data to the odd, four-period or high two-adic branch.
The fixed-Jacobi B2 check remains mandatory for the odd branch. -/
def rootPairFromChecked {n p k q g : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hperiod : primePowerIndex p k ∣ q - 1) (hnext : ¬primePowerIndex p (k + 1) ∣ q - 1)
    (hcop : Nat.Coprime g q) (hroot : primitiveRootCandidateTest q g = true) :
    Option (APRCLPairInput n) :=
  if htwo : p = 2 then
    if hk : k = 1 then
      some
        (.twoTwo (by decide)
          (datumFromCheckedRoot (by decide) hq (by simpa only [htwo, hk] using hperiod)
            (by simpa only [htwo, hk] using hnext) hcop hroot 1 1))
    else
      if hhigh : 2 ≤ k then
        some
          (.twoHigh (by decide) hhigh
            (highDataFromCheckedRoot hq (htwo ▸ hperiod) (htwo ▸ hnext) hcop hroot))
      else none
  else
    if hodd : 2 < p then
      if hb : aprclB2Check p = true then
        some
          (.odd hp hodd ((aprclB2Check_eq_true_iff p).mp hb)
            (datumFromCheckedRoot hp hq hperiod hnext hcop hroot 1 1))
      else none
    else none

/-- Construct a typed pair after checking prime parameters and exact period valuation.
This low-level builder has no resource limits; external callers use decodePairInput. -/
def buildPairInput (n : ℕ) (raw : RawPairData) : Option (APRCLPairInput n) :=
  if hp : Nat.Prime raw.p then
    if hq : Nat.Prime raw.q then
      if hperiod : primePowerIndex raw.p raw.k ∣ raw.q - 1 then
        if hnext : ¬primePowerIndex raw.p (raw.k + 1) ∣ raw.q - 1 then
          if raw.p = 2 ∧ raw.k = 0 then
            if hclass : raw.q % 4 = 3 then some (.twoOne raw.q hq hclass) else none
          else
            if raw.generator < raw.q then
              if hcop : Nat.Coprime raw.generator raw.q then
                if hroot : primitiveRootCandidateTest raw.q raw.generator = true then
                  rootPairFromChecked hp hq hperiod hnext hcop hroot
                else none
              else none
            else none
        else none
      else none
    else none
  else none

/-- Admissible bounded input for external pair construction.
Check integer bounds before the cyclotomic degree; require n above 1 and coprime to p and q. -/
abbrev RawPairData.WithinBounds (n : ℕ) (limits : PairInputLimits) (raw : RawPairData) : Prop :=
  raw.p ≤ limits.maxPrime ∧
    raw.q ≤ limits.maxPrime ∧
    raw.k ≤ limits.maxIndex ∧
    primePowerDegree raw.p raw.k ≤ limits.maxDegree ∧
    1 < n ∧ Nat.Coprime n raw.p ∧ Nat.Coprime n raw.q

/-- Recheck raw pair data under explicit limits and retain only its original key.
Failure means inadmissible data or an exceeded bound, not compositeness of n. -/
def decodePairInput (n : ℕ) (limits : PairInputLimits) (raw : RawPairData) :
    Option (APRCLPairInput n) :=
  if raw.WithinBounds n limits then
    (buildPairInput n raw).filter (fun input => decide (input.key = (raw.p, raw.k, raw.q)))
  else none

/-- Every decoded pair keeps exactly the supplied prime, index and auxiliary-prime key. -/
theorem decodePairInput_key {n : ℕ} {limits : PairInputLimits} {raw : RawPairData}
    {input : APRCLPairInput n} (h : decodePairInput n limits raw = some input) :
    input.key = (raw.p, raw.k, raw.q) := by
  unfold decodePairInput at h
  split at h
  · exact of_decide_eq_true (Option.filter_eq_some_iff.mp h).2
  · cases h

/-- Every successful decode satisfies the resource and input-coprimality guards. -/
theorem decodePairInput_bounds {n : ℕ} {limits : PairInputLimits} {raw : RawPairData}
    {input : APRCLPairInput n} (h : decodePairInput n limits raw = some input) :
    raw.WithinBounds n limits := by
  unfold decodePairInput at h
  split at h
  · assumption
  · cases h

/-- Decode every supplied row, rejecting an oversized list before pair construction.
A failed row rejects the entire list instead of silently dropping a required test. -/
def decodePairInputs (n : ℕ) (limits : PairInputLimits) (raws : List RawPairData) :
    Option (List (APRCLPairInput n)) :=
  if raws.length ≤ limits.maxPairs then raws.mapM (decodePairInput n limits) else none

/-- Use the rechecked initial condition and each typed pair as flag candidates.
These tags contain no claimed local-number-theoretic conclusion. -/
def pairFlagCandidates {n : ℕ} (entries : List (APRCLPairInput n)) : List (LpEvidenceData n) :=
  .initial :: entries.map .pair

/-- Check bounded raw data through the existing required-pair and flag verifier.
The parameter is positive, even and at most maxT before required keys are enumerated.
Acceptance is a finite-check result, not a primality verdict. -/
def checkRawPairs (n t : ℕ) (limits : PairInputLimits) (maxT : ℕ) (raws : List RawPairData) :
    Bool :=
  if 0 < t ∧ Even t ∧ t ≤ maxT then
    match decodePairInputs n limits raws with
    | none => false
    | some entries => checkRequiredWithFlags t entries (pairFlagCandidates entries)
  else false

/-- Raw acceptance yields the actual decoded rows and successful typed finite checking.
The existing local-number-theoretic obligations remain separate. -/
theorem checkRawPairs_spec {n t maxT : ℕ} {limits : PairInputLimits} {raws : List RawPairData}
    (h : checkRawPairs n t limits maxT raws = true) :
    0 < t ∧
      Even t ∧
      t ≤ maxT ∧
      ∃ entries,
        decodePairInputs n limits raws = some entries ∧
          checkRequiredWithFlags t entries (pairFlagCandidates entries) = true := by
  unfold checkRawPairs at h
  split at h
  · rename_i ht
    cases hd : decodePairInputs n limits raws with
    | none => simp only [hd, Bool.false_eq_true] at h
    | some entries => exact ⟨ht.1, ht.2.1, ht.2.2, entries, rfl, by simpa only [hd] using h⟩
  · exact Bool.noConfusion h

/-- Raw acceptance supplies checked flag sources for the existing conditional criterion.
The local block-congruence implication remains an explicit obligation of that criterion. -/
theorem checkRawPairs_sources {n t maxT : ℕ} {limits : PairInputLimits} {raws : List RawPairData}
    (h : checkRawPairs n t limits maxT raws = true) :
    ∃ entries,
      decodePairInputs n limits raws = some entries ∧
        checkRequiredWithFlags t entries (pairFlagCandidates entries) = true ∧
        checkedFlagSources t (pairFlagCandidates entries) := by
  obtain ⟨_, _, _, entries, hd, hc⟩ := checkRawPairs_spec h
  exact
    ⟨entries, hd, hc,
      checkRequiredWithFlags_sources_in_candidates entries (pairFlagCandidates entries) hc⟩

end PseudoPrime.PrimeTest.APRCL
