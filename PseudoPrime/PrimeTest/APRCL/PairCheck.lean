/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.APRCL.JacobiSum

/-!
# APR-CL pair checks and optional arithmetic flag guards

A root match is the main Jacobi test. The filtered exponent records when the same pair also
meets an arithmetic guard used for the local flag. Failure of that guard does not reject the
main test. The local number-theoretic implication is a separate proof obligation.
-/

namespace PseudoPrime.PrimeTest.APRCL

/-- The result of one APR-CL pair check. `mainExponent` records the root match;
`flagExponent` records the same match only when an arithmetic flag guard holds.
The invariant prevents a guard exponent without a main match. This record is used to keep
the four branch evaluators separate from the later local theorem and global aggregation. -/
structure APRCLPairCheckResult where
  /-- Least root exponent from the main finite test, if one exists. -/
  mainExponent : Option ℕ
  /-- The same exponent when this pair also passes its arithmetic flag guard. -/
  flagExponent : Option ℕ
  /-- A flag result preserves the exponent of the main test. -/
  flag_implies_main : ∀ h, flagExponent = some h → mainExponent = some h

/-- Construct a pair result by filtering the main exponent with a computable flag guard.
The filter keeps the exponent unchanged when the guard succeeds. -/
def APRCLPairCheckResult.ofFiltered (main : Option ℕ) (guard : ℕ → Bool) : APRCLPairCheckResult
    where
  mainExponent := main
  flagExponent := main.filter guard
  flag_implies_main := by
    intro h hh
    exact (Option.filter_eq_some_iff.mp hh).1

/-- Report whether the main Jacobi test found a root exponent. -/
def APRCLPairCheckResult.passed (result : APRCLPairCheckResult) : Bool :=
  result.mainExponent.isSome

/-- Report whether this pair also passed its arithmetic flag guard.
This Boolean alone does not prove the local number-theoretic condition. -/
def APRCLPairCheckResult.flagConditionMet (result : APRCLPairCheckResult) : Bool :=
  result.flagExponent.isSome

/-- A failed main test cannot pass the arithmetic flag guard for the same pair. -/
theorem APRCLPairCheckResult.flag_none_of_main_none (result : APRCLPairCheckResult)
    (hmain : result.mainExponent = none) : result.flagExponent = none := by
  cases hflag : result.flagExponent with
  | none => rfl
  | some h =>
    have hsome := result.flag_implies_main h hflag
    rw [hmain] at hsome
    cases hsome

/-- Passing the arithmetic flag guard implies that the main Jacobi test passed. -/
theorem APRCLPairCheckResult.flagConditionMet_imp_passed (result : APRCLPairCheckResult)
    (hflag : result.flagConditionMet = true) : result.passed = true := by
  cases hmain : result.mainExponent with
  | none =>
    have hnone := result.flag_none_of_main_none hmain
    simp only [APRCLPairCheckResult.flagConditionMet, hnone, Option.isSome_none] at hflag
    cases hflag
  | some h => simp only [APRCLPairCheckResult.passed, hmain, Option.isSome_some]

/-- Compute the low two-adic main sign test and separately retain its flag-guard exponent.
The raw auxiliary value `q` is checked by the later certificate boundary. -/
def aprclTwoAdicKOnePairResult (n q : ℕ) : APRCLPairCheckResult :=
  APRCLPairCheckResult.ofFiltered (aprclTwoAdicKOneCheck n q) (fun h => decide (h = 1 ∧ n % 4 = 1))

/-- The low two-adic pair result exposes the existing main and filtered checks. -/
theorem aprclTwoAdicKOnePairResult_spec (n q : ℕ) :
    (aprclTwoAdicKOnePairResult n q).mainExponent = aprclTwoAdicKOneCheck n q ∧
      (aprclTwoAdicKOnePairResult n q).flagExponent = aprclTwoAdicKOneBranchCheck n q := by
  exact ⟨rfl, rfl⟩

/-- A low two-adic main match has exactly the sign prescribed by its returned exponent;
this statement does not require the optional local-flag guard. -/
theorem aprclTwoAdicKOnePairResult_main_some_spec {n q h : ℕ}
    (hcheck : (aprclTwoAdicKOnePairResult n q).mainExponent = some h) :
    (h = 0 ∧ aprclTwoAdicKOneValue n q = 1) ∨ (h = 1 ∧ aprclTwoAdicKOneValue n q = -1) := by
  exact aprclTwoAdicKOneCheck_some_spec hcheck

/-- Compute the odd-prime main array test and its separate `p ∤ h` flag condition.
The datum supplies the checked character parameters and valuation. -/
def aprclOddPrimePairResult {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    APRCLPairCheckResult :=
  APRCLPairCheckResult.ofFiltered (aprclValidatedOddPrimeArrayCheck (n := n) hp hpOdd hB2 datum)
    (fun h => decide (h % p ≠ 0))

/-- The odd-prime pair result exposes its main root search and flag-guard filter. -/
theorem aprclOddPrimePairResult_spec {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    (aprclOddPrimePairResult (n := n) hp hpOdd hB2 datum).mainExponent =
        aprclValidatedOddPrimeArrayCheck (n := n) hp hpOdd hB2 datum ∧
      (aprclOddPrimePairResult (n := n) hp hpOdd hB2 datum).flagExponent =
        aprclValidatedOddPrimeArrayBranchCheck (n := n) hp hpOdd hB2 datum := by
  exact ⟨rfl, rfl⟩

/-- A main odd-prime match gives the Jacobi-product root equation and least
exponent, even when this pair does not establish its local flag. -/
theorem aprclOddPrimePairResult_main_some_spec {n p k h : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hpOdd : 2 < p) (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1)
    (hcheck : (aprclOddPrimePairResult (n := n) hp hpOdd hB2 datum).mainExponent = some h) :
    h < primePowerIndex p k ∧
      cyclotomicRoot n p k ^ h =
        ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
            (fun entry =>
              entry.jacobi.jacobiSumValue n hp ^
                (n * entry.productIndex / primePowerIndex p k))).prod ∧
      ∀ j < h,
        cyclotomicRoot n p k ^ j ≠
          ((aprclOddPrimeJacobiIndexFamily p k hpOdd datum.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex p k))).prod := by
  have hroot : aprclValidatedOddPrimeCheck (n := n) hp hpOdd hB2 datum = some h := by
    rw [← aprclValidatedOddPrimeArrayCheck_eq_check hn hp hpOdd hB2 datum]
    exact hcheck
  obtain ⟨hbound, hmatch, hminimal⟩ :=
    (aprclValidatedOddPrimeCheck_eq_some_iff hp hpOdd hB2 datum).mp hroot
  rw [aprclValidatedOddPrimeJacobiWeightedArray_class] at hmatch hminimal
  exact ⟨hbound, hmatch, hminimal⟩

/-- Compute the four-period main array test and retain its odd-exponent and Euler
local-flag condition. The datum carries its exact character and valuation evidence. -/
def aprclTwoAdicKTwoPairResult {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) : APRCLPairCheckResult :=
  APRCLPairCheckResult.ofFiltered (aprclValidatedTwoAdicKTwoArrayCheck (n := n) hp datum)
    (fun h => decide (h % 2 = 1 ∧ (datum.datum.q : ZMod n) ^ ((n - 1) / 2) = -1))

/-- The four-period pair result exposes its main search and flag-guard filter. -/
theorem aprclTwoAdicKTwoPairResult_spec {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    (aprclTwoAdicKTwoPairResult (n := n) hp datum).mainExponent =
        aprclValidatedTwoAdicKTwoArrayCheck (n := n) hp datum ∧
      (aprclTwoAdicKTwoPairResult (n := n) hp datum).flagExponent =
        aprclValidatedTwoAdicKTwoArrayBranchCheck (n := n) hp datum := by
  exact ⟨rfl, rfl⟩

/-- A four-period main match yields the least root exponent without requiring
the additional odd-exponent or Euler flag conditions. -/
theorem aprclTwoAdicKTwoPairResult_main_some_spec {n h : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1)
    (hcheck : (aprclTwoAdicKTwoPairResult (n := n) hp datum).mainExponent = some h) :
    h < primePowerIndex 2 1 ∧
      cyclotomicRoot n 2 1 ^ h = aprclValidatedTwoAdicKTwoValue hp datum ∧
      ∀ j < h, cyclotomicRoot n 2 1 ^ j ≠ aprclValidatedTwoAdicKTwoValue hp datum := by
  have hroot : aprclValidatedTwoAdicKTwoCheck (n := n) hp datum = some h := by
    rw [← aprclValidatedTwoAdicKTwoArrayCheck_eq_check hn hp datum]
    exact hcheck
  exact (aprclValidatedTwoAdicKTwoCheck_eq_some_iff hp datum).mp hroot

/-- Compute the high two-adic main array test and retain its odd-exponent and
Euler local-flag condition. The three Jacobi data share their checked generator. -/
def aprclTwoAdicHighPairResult {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) : APRCLPairCheckResult :=
  APRCLPairCheckResult.ofFiltered (aprclValidatedTwoAdicHighArrayCheck (n := n) hp hk data)
    (fun h => decide (h % 2 = 1 ∧ (data.auxiliaryPrime : ZMod n) ^ ((n - 1) / 2) = -1))

/-- The high two-adic pair result exposes its main search and flag-guard filter. -/
theorem aprclTwoAdicHighPairResult_spec {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) :
    (aprclTwoAdicHighPairResult (n := n) hp hk data).mainExponent =
        aprclValidatedTwoAdicHighArrayCheck (n := n) hp hk data ∧
      (aprclTwoAdicHighPairResult (n := n) hp hk data).flagExponent =
        aprclValidatedTwoAdicHighArrayBranchCheck (n := n) hp hk data := by
  exact ⟨rfl, rfl⟩

/-- A high two-adic main match gives the corrected Jacobi-product equation
and least exponent without requiring its optional local-flag guard. -/
theorem aprclTwoAdicHighPairResult_main_some_spec {n k h : ℕ} (hn : 1 < n) (hp : Nat.Prime 2)
    (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)
    (hcheck : (aprclTwoAdicHighPairResult (n := n) hp hk data).mainExponent = some h) :
    h < primePowerIndex 2 k ∧
      cyclotomicRoot n 2 k ^ h =
        ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
              (fun entry =>
                entry.jacobi.jacobiSumValue n hp ^
                  (n * entry.productIndex / primePowerIndex 2 k))).prod *
          data.datum₂.datum.jacobiSumValue n hp ^
            (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) ∧
      ∀ j < h,
        cyclotomicRoot n 2 k ^ j ≠
          ((aprclTwoAdicHighJacobiIndexFamily k hk data.datum₁₁.datum data.datum₂₁.datum).map
                (fun entry =>
                  entry.jacobi.jacobiSumValue n hp ^
                    (n * entry.productIndex / primePowerIndex 2 k))).prod *
            data.datum₂.datum.jacobiSumValue n hp ^
              (if aprclTwoAdicHighCorrectionFlag n then 2 else 0) := by
  have hroot : aprclValidatedTwoAdicHighCheck (n := n) hp hk data = some h := by
    rw [← aprclValidatedTwoAdicHighArrayCheck_eq_check hn hp hk data]
    exact hcheck
  obtain ⟨hbound, hmatch, hminimal⟩ :=
    (aprclValidatedTwoAdicHighCheck_eq_some_iff hp hk data).mp hroot
  rw [aprclValidatedTwoAdicHighBranchArray_class] at hmatch hminimal
  exact ⟨hbound, hmatch, hminimal⟩

/-- A typed input for one of the four APR-CL Jacobi test formulas. The low two-adic
case carries a prime `q ≡ 3 mod 4`; the other constructors carry their checked
character and valuation data. Global pair coverage remains a separate requirement. -/
inductive APRCLPairInput (n : ℕ) where
  /-- The scalar `p=2,k=1` formula. -/
  | twoOne (q : ℕ) (hqPrime : Nat.Prime q) (hqClass : q % 4 = 3)
  /-- The odd-prime Jacobi product with the fixed `J₁,₁` condition. -/
  |
  odd {p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p) (hB2 : aprclB2Condition p)
    (datum : APRCLJacobiDatumWithParameters p k 1 1)
  /-- The four-period `p=2,k=2` formula. -/
  | twoTwo (hp : Nat.Prime 2) (datum : APRCLJacobiDatumWithParameters 2 1 1 1)
  /-- The corrected high two-adic Jacobi product. -/
  | twoHigh {k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k) (data : APRCLTwoAdicHighBranchData k)

/-- Dispatch one typed pair to its computable main test and optional flag-guard
condition. The result is a pair test, not a primality verdict. -/
def APRCLPairInput.check {n : ℕ} : APRCLPairInput n → APRCLPairCheckResult
  | .twoOne q _ _ => aprclTwoAdicKOnePairResult n q
  | .odd hp hpOdd hB2 datum => aprclOddPrimePairResult (n := n) hp hpOdd hB2 datum
  | .twoTwo hp datum => aprclTwoAdicKTwoPairResult (n := n) hp datum
  | .twoHigh hp hk data => aprclTwoAdicHighPairResult (n := n) hp hk data

/-- Dispatching the low two-adic constructor uses its scalar pair test. -/
theorem APRCLPairInput.check_twoOne {n q : ℕ} (hqPrime : Nat.Prime q) (hqClass : q % 4 = 3) :
    (APRCLPairInput.twoOne (n := n) q hqPrime hqClass).check = aprclTwoAdicKOnePairResult n q :=
  rfl

/-- Dispatching the odd-prime constructor uses its validated array pair test. -/
theorem APRCLPairInput.check_odd {n p k : ℕ} (hp : Nat.Prime p) (hpOdd : 2 < p)
    (hB2 : aprclB2Condition p) (datum : APRCLJacobiDatumWithParameters p k 1 1) :
    (APRCLPairInput.odd (n := n) hp hpOdd hB2 datum).check =
      aprclOddPrimePairResult (n := n) hp hpOdd hB2 datum :=
  rfl

/-- Dispatching the four-period constructor uses its validated array pair test. -/
theorem APRCLPairInput.check_twoTwo {n : ℕ} (hp : Nat.Prime 2)
    (datum : APRCLJacobiDatumWithParameters 2 1 1 1) :
    (APRCLPairInput.twoTwo (n := n) hp datum).check =
      aprclTwoAdicKTwoPairResult (n := n) hp datum :=
  rfl

/-- Dispatching the high two-adic constructor uses its corrected array pair test. -/
theorem APRCLPairInput.check_twoHigh {n k : ℕ} (hp : Nat.Prime 2) (hk : 2 ≤ k)
    (data : APRCLTwoAdicHighBranchData k) :
    (APRCLPairInput.twoHigh (n := n) hp hk data).check =
      aprclTwoAdicHighPairResult (n := n) hp hk data :=
  rfl

/-- Whichever of the four formulas is dispatched, a flag-guard result certifies
that its main Jacobi test passed. -/
theorem APRCLPairInput.check_flagConditionMet_imp_passed {n : ℕ} (input : APRCLPairInput n)
    (hflag : input.check.flagConditionMet = true) : input.check.passed = true := by
  exact APRCLPairCheckResult.flagConditionMet_imp_passed input.check hflag

/-- Check that every supplied pair passes its main Jacobi test.
This finite list may omit required pairs; coverage is checked at the certificate boundary. -/
def APRCLPairInput.allMainPassed {n : ℕ} (entries : List (APRCLPairInput n)) : Bool :=
  entries.all (fun input => input.check.passed)

/-- The finite main-test aggregate succeeds exactly when every supplied pair succeeds. -/
theorem APRCLPairInput.allMainPassed_eq_true_iff {n : ℕ} (entries : List (APRCLPairInput n)) :
    APRCLPairInput.allMainPassed entries = true ↔ ∀ input ∈ entries, input.check.passed = true := by
  exact List.all_eq_true

/-- Find whether one supplied pair passes its arithmetic flag guard.
This Boolean does not prove the local number-theoretic flag condition. -/
def APRCLPairInput.anyFlagGuardMet {n : ℕ} (entries : List (APRCLPairInput n)) : Bool :=
  entries.any (fun input => input.check.flagConditionMet)

/-- The finite flag-guard aggregate succeeds exactly when a supplied pair passes its guard. -/
theorem APRCLPairInput.anyFlagGuardMet_eq_true_iff {n : ℕ} (entries : List (APRCLPairInput n)) :
    APRCLPairInput.anyFlagGuardMet entries = true ↔
      ∃ input ∈ entries, input.check.flagConditionMet = true := by
  exact List.any_eq_true

/-- A guard success in a supplied pair list includes a successful main test for that pair. -/
theorem APRCLPairInput.anyFlagGuardMet_main {n : ℕ} (entries : List (APRCLPairInput n))
    (hguard : APRCLPairInput.anyFlagGuardMet entries = true) :
    ∃ input ∈ entries, input.check.passed = true := by
  obtain ⟨input, hin, hflag⟩ := (APRCLPairInput.anyFlagGuardMet_eq_true_iff entries).mp hguard
  exact ⟨input, hin, input.check_flagConditionMet_imp_passed hflag⟩

/-- Identify a supplied pair by its cyclotomic prime, zero-based power index, and auxiliary
prime. The four constructors retain these values for the certificate coverage check. -/
def APRCLPairInput.key {n : ℕ} : APRCLPairInput n → ℕ × ℕ × ℕ
  | .twoOne q _ _ => (2, 0, q)
  | .odd (p := p) (k := k) _ _ _ datum => (p, k, datum.datum.q)
  | .twoTwo _ datum => (2, 1, datum.datum.q)
  | .twoHigh (k := k) _ _ data => (2, k, data.auxiliaryPrime)

/-- Check whether a supplied list contains an input for one specified pair key. -/
def APRCLPairInput.coversKey {n : ℕ} (entries : List (APRCLPairInput n)) (key : ℕ × ℕ × ℕ) : Bool :=
  entries.any (fun input => decide (input.key = key))

/-- The key check succeeds exactly when a matching typed pair is present. -/
theorem APRCLPairInput.coversKey_eq_true_iff {n : ℕ} (entries : List (APRCLPairInput n))
    (key : ℕ × ℕ × ℕ) :
    APRCLPairInput.coversKey entries key = true ↔ ∃ input ∈ entries, input.key = key := by
  rw [APRCLPairInput.coversKey, List.any_eq_true]
  simp only [decide_eq_true_eq]

/-- Check every key supplied by a later parameter and coverage certificate. The caller must
still establish that its `required` list contains all mathematically required pairs. -/
def APRCLPairInput.allKeysCovered {n : ℕ} (entries : List (APRCLPairInput n))
    (required : List (ℕ × ℕ × ℕ)) : Bool :=
  required.all (APRCLPairInput.coversKey entries)

/-- The finite coverage check has an exact membership specification. -/
theorem APRCLPairInput.allKeysCovered_eq_true_iff {n : ℕ} (entries : List (APRCLPairInput n))
    (required : List (ℕ × ℕ × ℕ)) :
    APRCLPairInput.allKeysCovered entries required = true ↔
      ∀ key ∈ required, ∃ input ∈ entries, input.key = key := by
  rw [APRCLPairInput.allKeysCovered, List.all_eq_true]
  simp only [APRCLPairInput.coversKey_eq_true_iff]

/-- A covered key has a passing main Jacobi test when the whole supplied list passes. -/
theorem APRCLPairInput.allKeysCovered_main {n : ℕ} (entries : List (APRCLPairInput n))
    (required : List (ℕ × ℕ × ℕ)) (hcover : APRCLPairInput.allKeysCovered entries required = true)
    (hmain : APRCLPairInput.allMainPassed entries = true) :
    ∀ key ∈ required, ∃ input ∈ entries, input.key = key ∧ input.check.passed = true := by
  intro key hkey
  obtain ⟨input, hin, hmatch⟩ :=
    (APRCLPairInput.allKeysCovered_eq_true_iff entries required).mp hcover key hkey
  exact ⟨input, hin, hmatch, (APRCLPairInput.allMainPassed_eq_true_iff entries).mp hmain input hin⟩

/-- Check listed coverage and all main tests together. Required keys need separate justification. -/
def APRCLPairInput.checkRequired {n : ℕ} (entries : List (APRCLPairInput n))
    (required : List (ℕ × ℕ × ℕ)) : Bool :=
  APRCLPairInput.allKeysCovered entries required && APRCLPairInput.allMainPassed entries

/-- Acceptance supplies a passing main test for every required key. -/
theorem APRCLPairInput.checkRequired_main {n : ℕ} (entries : List (APRCLPairInput n))
    (required : List (ℕ × ℕ × ℕ)) (hcheck : APRCLPairInput.checkRequired entries required = true) :
    ∀ key ∈ required, ∃ input ∈ entries, input.key = key ∧ input.check.passed = true := by
  simp only [APRCLPairInput.checkRequired, Bool.and_eq_true] at hcheck
  exact APRCLPairInput.allKeysCovered_main entries required hcheck.1 hcheck.2

/-- Enumerate the pairs required by the APR-CL main test for parameter `t`: every odd
auxiliary prime and every distinct prime divisor of its predecessor. The backend index is
one less than the exact valuation of `q - 1`. -/
def requiredPairKeys (t : ℕ) : List (ℕ × ℕ × ℕ) :=
  ((auxiliaryPrimeSearch t).filter (fun q => decide (2 < q))).flatMap
    (fun q =>
      ((q - 1).primeFactors.sort (· ≤ ·)).map (fun p => (p, Nat.factorization (q - 1) p - 1, q)))

/-- Membership in the executable required-key list has the exact auxiliary-prime and
prime-factor specification. -/
theorem mem_requiredPairKeys_iff {t p k q : ℕ} :
    (p, k, q) ∈ requiredPairKeys t ↔
      q ∈ auxiliaryPrimeSearch t ∧
        2 < q ∧ p ∈ (q - 1).primeFactors ∧ k = Nat.factorization (q - 1) p - 1 := by
  simp only [requiredPairKeys, List.mem_flatMap, List.mem_map, List.mem_filter, decide_eq_true_eq,
    Finset.mem_sort]
  constructor
  · rintro ⟨q', ⟨hq', hodd⟩, p', hp', heq⟩
    cases heq
    exact ⟨hq', hodd, hp', rfl⟩
  · rintro ⟨hq, hodd, hp, hk⟩
    exact ⟨q, ⟨hq, hodd⟩, p, hp, by rw [hk]⟩

/-- A required key has a prime auxiliary modulus and its zero-based index recovers the
exact prime-adic valuation of the predecessor. -/
theorem mem_requiredPairKeys_spec {t p k q : ℕ} (ht : t ≠ 0)
    (hkey : (p, k, q) ∈ requiredPairKeys t) :
    Nat.Prime q ∧
      q - 1 ∣ t ∧ 2 < q ∧ Nat.Prime p ∧ p ∣ q - 1 ∧ k + 1 = Nat.factorization (q - 1) p := by
  obtain ⟨hq, hodd, hp, hk⟩ := mem_requiredPairKeys_iff.mp hkey
  obtain ⟨hqprime, hqdiv⟩ := (mem_auxiliaryPrimeSearch_iff_prime_sub_dvd ht).mp hq
  obtain ⟨hpprime, hpdiv, hqne⟩ := Nat.mem_primeFactors.mp hp
  have hval : 0 < Nat.factorization (q - 1) p := hpprime.factorization_pos_of_dvd hqne hpdiv
  refine ⟨hqprime, hqdiv, hodd, hpprime, hpdiv, ?_⟩
  rw [hk]
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hval)

/-- A parameter-derived pair key uses a prime power that divides the APR-CL parameter. -/
theorem primePowerIndex_dvd_t_of_mem_requiredPairKeys {t p k q : ℕ} (ht : t ≠ 0)
    (hkey : (p, k, q) ∈ requiredPairKeys t) : primePowerIndex p k ∣ t := by
  obtain ⟨_, hqdiv, hodd, hpprime, _, hval⟩ := mem_requiredPairKeys_spec ht hkey
  have hqne : q - 1 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr (Nat.lt_trans Nat.one_lt_two hodd)
  have hpow : p ^ (k + 1) ∣ q - 1 := (hpprime.pow_dvd_iff_le_factorization hqne).mpr (by rw [hval])
  exact dvd_trans hpow hqdiv

/-- A single exponent below `t` realizes prescribed residues at every
parameter-derived pair key. The backend index `k` uses modulus `p^(k+1)`;
its divisibility into `t` lets the prime-power CRT exponent restrict to it.
This connects finite key enumeration to the common-exponent interface. -/
theorem commonExponent_mod_requiredPairKeys {t : ℕ} (ht : t ≠ 0) (a : ℕ → ℕ) :
    ∃ i,
      i < t ∧
        ∀ p k q, (p, k, q) ∈ requiredPairKeys t → Nat.ModEq (primePowerIndex p k) i (a p) := by
  obtain ⟨i, hit, hres⟩ := exists_commonExponent_mod_primePowers ht a
  refine ⟨i, hit, ?_⟩
  intro p k q hkey
  obtain ⟨_, hqdiv, _, hpprime, hpdiv, _⟩ := mem_requiredPairKeys_spec ht hkey
  have hpt : p ∣ t := dvd_trans hpdiv hqdiv
  have hpMem : p ∈ t.primeFactors := Nat.mem_primeFactors.mpr ⟨hpprime, hpt, ht⟩
  have hpow := primePowerIndex_dvd_t_of_mem_requiredPairKeys ht hkey
  change p ^ (k + 1) ∣ t at hpow
  have hle : k + 1 ≤ Nat.factorization t p := (hpprime.pow_dvd_iff_le_factorization ht).mp hpow
  exact Nat.ModEq.of_dvd (pow_dvd_pow p hle) (hres p hpMem)

/-- Passing the parameter-derived check supplies every odd auxiliary-prime and prime-power
main test required by the APR-CL pair stage. -/
theorem APRCLPairInput.checkRequired_parameter_main {n t : ℕ} (entries : List (APRCLPairInput n))
    (hcheck : APRCLPairInput.checkRequired entries (requiredPairKeys t) = true) :
    ∀ q ∈ auxiliaryPrimeSearch t,
      2 < q →
        ∀ p ∈ (q - 1).primeFactors,
          ∃ input ∈ entries,
            input.key = (p, Nat.factorization (q - 1) p - 1, q) ∧ input.check.passed = true := by
  intro q hq hodd p hp
  apply APRCLPairInput.checkRequired_main entries (requiredPairKeys t) hcheck
  exact mem_requiredPairKeys_iff.mpr ⟨hq, hodd, hp, rfl⟩

/-- Each accepted required key has its prime-power index in the parameter and a
passing typed main-test input. This connects finite coverage to the APR-CL modulus. -/
theorem APRCLPairInput.checkRequired_parameter_power_main {n t : ℕ}
    (entries : List (APRCLPairInput n)) (ht : t ≠ 0)
    (hcheck : APRCLPairInput.checkRequired entries (requiredPairKeys t) = true) :
    ∀ p k q,
      (p, k, q) ∈ requiredPairKeys t →
        primePowerIndex p k ∣ t ∧
          ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true := by
  intro p k q hkey
  constructor
  · exact primePowerIndex_dvd_t_of_mem_requiredPairKeys ht hkey
  · exact APRCLPairInput.checkRequired_main entries (requiredPairKeys t) hcheck (p, k, q) hkey

/-- Candidate data for obtaining the APR-CL flag at prime `p`. The initial tag
rechecks the odd-prime congruence; the pair tag retains a typed Jacobi input.
Neither tag by itself proves the local number-theoretic condition. -/
inductive LpEvidenceData (n : ℕ) where
  /-- The initial odd-prime congruence is to be rechecked for the requested `p`. -/
  | initial
  /-- A pair input whose arithmetic flag guard is to be rechecked. -/
  | pair (input : APRCLPairInput n)

/-- Recheck a proposed flag source for `p ∣ t`. Initial evidence uses (L-init);
pair evidence matches `p` and reruns its arithmetic guard. -/
def LpEvidenceData.check {n : ℕ} (t p : ℕ) : LpEvidenceData n → Bool
  | .initial => decide (Nat.Prime p ∧ 2 < p ∧ p ∣ t ∧ n ^ (p - 1) % p ^ 2 ≠ 1)
  | .pair input => decide (input.key.1 = p) && input.check.flagConditionMet

/-- The initial tag succeeds exactly under the odd-prime (L-init) condition. -/
theorem LpEvidenceData.check_initial_iff {n t p : ℕ} :
    (LpEvidenceData.initial : LpEvidenceData n).check t p = true ↔
      Nat.Prime p ∧ 2 < p ∧ p ∣ t ∧ n ^ (p - 1) % p ^ 2 ≠ 1 := by
  simp only [LpEvidenceData.check, decide_eq_true_eq]

/-- A pair tag succeeds exactly when its key matches `p` and its arithmetic
flag guard succeeds. The local number-theoretic implication remains separate. -/
theorem LpEvidenceData.check_pair_iff {n t p : ℕ} (input : APRCLPairInput n) :
    (LpEvidenceData.pair input).check t p = true ↔
      input.key.1 = p ∧ input.check.flagConditionMet = true := by
  simp only [LpEvidenceData.check, Bool.and_eq_true, decide_eq_true_eq]

/-- A checked pair tag also has a passing main Jacobi test. -/
theorem LpEvidenceData.check_pair_main {n t p : ℕ} (input : APRCLPairInput n)
    (hcheck : (LpEvidenceData.pair input).check t p = true) :
    input.key.1 = p ∧ input.check.passed = true := by
  obtain ⟨hkey, hflag⟩ := (LpEvidenceData.check_pair_iff input).mp hcheck
  exact ⟨hkey, input.check_flagConditionMet_imp_passed hflag⟩

/-- A checked flag candidate exposes exactly the initial congruence or a
matching pair with successful arithmetic guard and main Jacobi test. -/
theorem LpEvidenceData.check_true_cases {n t p : ℕ} (evidence : LpEvidenceData n)
    (hcheck : evidence.check t p = true) :
    (Nat.Prime p ∧ 2 < p ∧ p ∣ t ∧ n ^ (p - 1) % p ^ 2 ≠ 1) ∨
      ∃ input : APRCLPairInput n,
        evidence = .pair input ∧
          input.key.1 = p ∧ input.check.flagConditionMet = true ∧ input.check.passed = true := by
  cases evidence with
  | initial => exact Or.inl (LpEvidenceData.check_initial_iff.mp hcheck)
  | pair input =>
    obtain ⟨hkey, hflag⟩ := (LpEvidenceData.check_pair_iff input).mp hcheck
    exact Or.inr ⟨input, rfl, hkey, hflag, input.check_flagConditionMet_imp_passed hflag⟩

/-- Keep a previously obtained candidate when the new one fails rechecking. -/
def LpEvidenceData.update {n : ℕ} (t p : ℕ) (old : Option (LpEvidenceData n))
    (candidate : LpEvidenceData n) : Option (LpEvidenceData n) :=
  if candidate.check t p then some candidate else old

/-- An unsuccessful candidate cannot erase previously retained flag data. -/
theorem LpEvidenceData.update_preserves_old {n t p : ℕ} (old : Option (LpEvidenceData n))
    (candidate : LpEvidenceData n) (hfail : candidate.check t p = false) :
    candidate.update t p old = old := by
  simp only [LpEvidenceData.update, hfail, Bool.false_eq_true, ↓reduceIte]

/-- A sequence step preserves the invariant that every retained candidate passes
its executable recheck. This does not establish the local APR-CL flag theorem. -/
theorem LpEvidenceData.update_checked {n t p : ℕ} (old : Option (LpEvidenceData n))
    (candidate : LpEvidenceData n)
    (hold : ∀ evidence, old = some evidence → evidence.check t p = true) :
    ∀ evidence, candidate.update t p old = some evidence → evidence.check t p = true := by
  intro evidence hresult
  cases hcheck : candidate.check t p with
  | false =>
    simp only [LpEvidenceData.update, hcheck, Bool.false_eq_true, ↓reduceIte] at hresult
    exact hold evidence hresult
  | true =>
    simp only [LpEvidenceData.update, hcheck, ↓reduceIte, Option.some.injEq] at hresult
    rw [← hresult]
    exact hcheck

/-- Collect the first rechecked flag candidate from a finite list. The result is
`none` when no candidate passes. A successful head returns immediately without
evaluating the checks on the remaining candidates. -/
def LpEvidenceData.collect {n : ℕ} (t p : ℕ) : List (LpEvidenceData n) → Option (LpEvidenceData n)
  | [] => none
  | candidate :: rest =>
    if candidate.check t p then some candidate else LpEvidenceData.collect t p rest

/-- Candidate collection has the exact first-success semantics of `List.find?`.
This also identifies the returned candidate, not only the existence of a success. -/
theorem LpEvidenceData.collect_eq_find {n t p : ℕ} (candidates : List (LpEvidenceData n)) :
    LpEvidenceData.collect t p candidates =
      candidates.find? (fun evidence => evidence.check t p) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    rw [LpEvidenceData.collect, List.find?_cons, ← ih]
    cases candidate.check t p <;> rfl

/-- Every returned flag candidate belongs to the supplied finite candidate list. -/
theorem LpEvidenceData.collect_some_mem {n t p : ℕ} {candidates : List (LpEvidenceData n)}
    {evidence : LpEvidenceData n} (h : LpEvidenceData.collect t p candidates = some evidence) :
    evidence ∈ candidates := by
  rw [LpEvidenceData.collect_eq_find] at h
  exact List.mem_of_find?_eq_some h

/-- Every result of finite candidate collection passes its executable recheck. -/
theorem LpEvidenceData.collect_checked {n t p : ℕ} (candidates : List (LpEvidenceData n)) :
    ∀ evidence,
      LpEvidenceData.collect t p candidates = some evidence → evidence.check t p = true := by
  induction candidates with
  | nil =>
    intro evidence hresult
    cases hresult
  | cons candidate rest ih =>
    exact LpEvidenceData.update_checked (LpEvidenceData.collect t p rest) candidate ih

/-- Finite flag collection succeeds exactly when some candidate passes its recheck. -/
theorem LpEvidenceData.collect_isSome_eq_any {n t p : ℕ} (candidates : List (LpEvidenceData n)) :
    (LpEvidenceData.collect t p candidates).isSome =
      candidates.any (fun evidence => evidence.check t p) := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
    cases hcheck : candidate.check t p with
    | false =>
      simp only [LpEvidenceData.collect, hcheck, Bool.false_eq_true, ↓reduceIte, List.any_cons,
        Bool.false_or]
      exact ih
    | true =>
      simp only [LpEvidenceData.collect, hcheck, ↓reduceIte, Option.isSome_some, List.any_cons,
        Bool.true_or]

/-- Enumerate the distinct primes whose APR-CL flags are required by parameter `t`.
The zero parameter is rejected by the aggregate checker below. -/
def requiredFlagPrimes (t : ℕ) : List ℕ :=
  t.primeFactors.sort (· ≤ ·)

/-- Membership in the finite flag list is exactly prime divisibility of nonzero `t`. -/
theorem mem_requiredFlagPrimes_iff {t p : ℕ} :
    p ∈ requiredFlagPrimes t ↔ Nat.Prime p ∧ p ∣ t ∧ t ≠ 0 := by
  rw [requiredFlagPrimes, Finset.mem_sort]
  exact Nat.mem_primeFactors

/-- Require a checked flag candidate for each distinct prime dividing nonzero `t`.
This checks evidence data only; A5 must still prove its local mathematical meaning. -/
def LpEvidenceData.allRequiredChecked {n : ℕ} (t : ℕ) (candidates : List (LpEvidenceData n)) :
    Bool :=
  decide (t ≠ 0) &&
    (requiredFlagPrimes t).all (fun p => (LpEvidenceData.collect t p candidates).isSome)

/-- The aggregate succeeds exactly when every required prime has a candidate
that passes its executable recheck. -/
theorem LpEvidenceData.allRequiredChecked_iff {n t : ℕ} (candidates : List (LpEvidenceData n)) :
    LpEvidenceData.allRequiredChecked t candidates = true ↔
      t ≠ 0 ∧
        ∀ p,
          Nat.Prime p →
            p ∣ t →
            ∃ evidence,
              LpEvidenceData.collect t p candidates = some evidence ∧
                evidence.check t p = true := by
  rw [LpEvidenceData.allRequiredChecked, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    intro p hp hdiv
    have hmem : p ∈ requiredFlagPrimes t := mem_requiredFlagPrimes_iff.mpr ⟨hp, hdiv, ht⟩
    obtain ⟨evidence, hsome⟩ := Option.isSome_iff_exists.mp (h p hmem)
    exact ⟨evidence, hsome, LpEvidenceData.collect_checked candidates evidence hsome⟩
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    intro p hmem
    obtain ⟨hp, hdiv, _⟩ := mem_requiredFlagPrimes_iff.mp hmem
    obtain ⟨evidence, hsome, _⟩ := h p hp hdiv
    exact Option.isSome_iff_exists.mpr ⟨evidence, hsome⟩

/-- Aggregate flag acceptance is equivalent to a passing candidate in the supplied finite list
for every prime dividing the nonzero parameter. -/
theorem LpEvidenceData.allRequiredChecked_iff_candidates {n t : ℕ}
    (candidates : List (LpEvidenceData n)) :
    LpEvidenceData.allRequiredChecked t candidates = true ↔
      t ≠ 0 ∧ ∀ p, Nat.Prime p → p ∣ t → ∃ evidence ∈ candidates, evidence.check t p = true := by
  rw [LpEvidenceData.allRequiredChecked_iff]
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    intro p hp hdiv
    obtain ⟨evidence, hsome, _⟩ := h p hp hdiv
    have hfound : candidates.any (fun e => e.check t p) = true := by
      rw [← LpEvidenceData.collect_isSome_eq_any]
      exact Option.isSome_iff_exists.mpr ⟨evidence, hsome⟩
    exact List.any_eq_true.mp hfound
  · rintro ⟨ht, h⟩
    refine ⟨ht, ?_⟩
    intro p hp hdiv
    have hfound : (LpEvidenceData.collect t p candidates).isSome = true := by
      rw [LpEvidenceData.collect_isSome_eq_any]
      exact List.any_eq_true.mpr (h p hp hdiv)
    obtain ⟨evidence, hsome⟩ := Option.isSome_iff_exists.mp hfound
    exact ⟨evidence, hsome, LpEvidenceData.collect_checked candidates evidence hsome⟩

/-- Check the parameter-derived main tests and every required prime's flag
candidate together. Passing still requires A5/A6 before a primality verdict. -/
def checkRequiredWithFlags {n : ℕ} (t : ℕ) (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n)) : Bool :=
  APRCLPairInput.checkRequired entries (requiredPairKeys t) &&
    LpEvidenceData.allRequiredChecked t candidates

/-- Exact finite acceptance contract: key coverage, all supplied main tests,
nonzero parameter, and one checked candidate per prime divisor. -/
theorem checkRequiredWithFlags_iff {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n)) :
    checkRequiredWithFlags t entries candidates = true ↔
      (∀ key ∈ requiredPairKeys t, ∃ input ∈ entries, input.key = key) ∧
        (∀ input ∈ entries, input.check.passed = true) ∧
        t ≠ 0 ∧
        (∀ p,
          Nat.Prime p →
            p ∣ t →
            ∃ evidence,
              LpEvidenceData.collect t p candidates = some evidence ∧
                evidence.check t p = true) := by
  simp only [checkRequiredWithFlags, Bool.and_eq_true, APRCLPairInput.checkRequired,
    APRCLPairInput.allKeysCovered_eq_true_iff, APRCLPairInput.allMainPassed_eq_true_iff,
    LpEvidenceData.allRequiredChecked_iff, and_assoc]

/-- The finite acceptance contract can be stated directly in terms of supplied candidates:
every required prime has a candidate that passes the executable recheck. -/
theorem checkRequiredWithFlags_iff_candidates {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n)) :
    checkRequiredWithFlags t entries candidates = true ↔
      (∀ key ∈ requiredPairKeys t, ∃ input ∈ entries, input.key = key) ∧
        (∀ input ∈ entries, input.check.passed = true) ∧
        t ≠ 0 ∧
        (∀ p, Nat.Prime p → p ∣ t → ∃ evidence ∈ candidates, evidence.check t p = true) := by
  simp only [checkRequiredWithFlags, Bool.and_eq_true, APRCLPairInput.checkRequired,
    APRCLPairInput.allKeysCovered_eq_true_iff, APRCLPairInput.allMainPassed_eq_true_iff,
    LpEvidenceData.allRequiredChecked_iff_candidates, and_assoc]

/-- The combined finite check yields all required prime-power main tests and
one rechecked flag candidate per prime dividing `t`. -/
theorem checkRequiredWithFlags_spec {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) :
    t ≠ 0 ∧
      (∀ p k q,
        (p, k, q) ∈ requiredPairKeys t →
          primePowerIndex p k ∣ t ∧
            ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true) ∧
      (∀ p,
        Nat.Prime p →
          p ∣ t →
          ∃ evidence,
            LpEvidenceData.collect t p candidates = some evidence ∧ evidence.check t p = true) := by
  have hparts :
    APRCLPairInput.checkRequired entries (requiredPairKeys t) = true ∧
      LpEvidenceData.allRequiredChecked t candidates = true := by
    simpa only [checkRequiredWithFlags, Bool.and_eq_true] using hcheck
  obtain ⟨ht, hflags⟩ := (LpEvidenceData.allRequiredChecked_iff candidates).mp hparts.2
  exact ⟨ht, APRCLPairInput.checkRequired_parameter_power_main entries ht hparts.1, hflags⟩

/-- A successful finite main-and-flag check supplies a common exponent for any
prescribed local residues at all required pair keys, together with a passing
typed main-test input for each key. The exponent congruences are arithmetic
CRT data; local Gauss/Frobenius implications remain a separate obligation. -/
theorem checkRequiredWithFlags_commonExponent {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) (a : ℕ → ℕ) :
    ∃ i,
      i < t ∧
        ∀ p k q,
          (p, k, q) ∈ requiredPairKeys t →
            Nat.ModEq (primePowerIndex p k) i (a p) ∧
              ∃ input ∈ entries, input.key = (p, k, q) ∧ input.check.passed = true := by
  obtain ⟨ht, hmain, _⟩ := checkRequiredWithFlags_spec entries candidates hcheck
  obtain ⟨i, hit, hmod⟩ := commonExponent_mod_requiredPairKeys ht a
  refine ⟨i, hit, ?_⟩
  intro p k q hkey
  exact ⟨hmod p k q hkey, (hmain p k q hkey).2⟩

/-- Every required prime has a checked source in the supplied candidate list.
The initial congruence and pair guard still require the A5 local implication. -/
theorem checkRequiredWithFlags_sources_in_candidates {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) :
    ∀ p,
      Nat.Prime p →
        p ∣ t →
        (2 < p ∧
            n ^ (p - 1) % p ^ 2 ≠ 1 ∧ (LpEvidenceData.initial : LpEvidenceData n) ∈ candidates) ∨
          ∃ input : APRCLPairInput n,
            LpEvidenceData.pair input ∈ candidates ∧
              input.key.1 = p ∧
              input.check.flagConditionMet = true ∧ input.check.passed = true := by
  intro p hp hdiv
  obtain ⟨_, _, _, hflags⟩ := (checkRequiredWithFlags_iff_candidates entries candidates).mp hcheck
  obtain ⟨evidence, hmem, hchecked⟩ := hflags p hp hdiv
  cases evidence with
  | initial =>
    obtain ⟨_, hpOdd, _, hneq⟩ := LpEvidenceData.check_initial_iff.mp hchecked
    exact Or.inl ⟨hpOdd, hneq, hmem⟩
  | pair input =>
    obtain ⟨hkey, hflag⟩ := (LpEvidenceData.check_pair_iff input).mp hchecked
    exact Or.inr ⟨input, hmem, hkey, hflag, input.check_flagConditionMet_imp_passed hflag⟩

/-- Every required prime has either the odd-prime initial congruence or a
matching pair whose guard and main Jacobi test passed. -/
theorem checkRequiredWithFlags_sources {n t : ℕ} (entries : List (APRCLPairInput n))
    (candidates : List (LpEvidenceData n))
    (hcheck : checkRequiredWithFlags t entries candidates = true) :
    ∀ p,
      Nat.Prime p →
        p ∣ t →
        (2 < p ∧ n ^ (p - 1) % p ^ 2 ≠ 1) ∨
          ∃ input : APRCLPairInput n,
            input.key.1 = p ∧ input.check.flagConditionMet = true ∧ input.check.passed = true := by
  intro p hp hdiv
  rcases checkRequiredWithFlags_sources_in_candidates entries candidates hcheck p hp hdiv with hin |
    hpair
  · exact Or.inl ⟨hin.1, hin.2.1⟩
  · obtain ⟨input, _, hkey, hflag, hmain⟩ := hpair
    exact Or.inr ⟨input, hkey, hflag, hmain⟩

end PseudoPrime.PrimeTest.APRCL
