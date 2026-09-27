/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.PrimeTest.FactorizationPolicy
import PseudoPrime.NumberTheory.Factorization.PollardRho.FactorSupply
import PseudoPrime.NumberTheory.Factorization.PrimePowers
import PseudoPrime.PrimeTest.BLS.Basic
import PseudoPrime.NumberTheory.Factorization.PollardRho.Basic

/-!
# Pollard rho factor hints for BLS

This module uses a bounded Pollard rho attempt on `n - 1` to supply a proper split. The returned
divisor can be composite; BLS certificate construction must separately factor and certify its keys.
-/

namespace PseudoPrime.PrimeTest.BLS

/-- Find a bounded nontrivial divisor of `n - 1` and return it with its complementary cofactor. -/
def findNMinusOneFactor (n : ℕ) (params :
    NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) :
    Option (ℕ × ℕ) :=
  (PseudoPrime.NumberTheory.Factorization.PollardRho.findFactor (n - 1) params fuel).map
    (fun d => (d, (n - 1) / d))

/-- A rho factor hint is a proper two-part decomposition of `n - 1`; neither part is claimed prime.
The `none` case means that this one bounded rho schedule did not find a split. -/
theorem findNMinusOneFactor_sound {n d r : ℕ} {params :
    NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    (h : findNMinusOneFactor n params fuel = some (d, r)) :
    1 < d ∧ 1 < r ∧ d * r = n - 1 := by
  unfold findNMinusOneFactor at h
  cases hfind : PseudoPrime.NumberTheory.Factorization.PollardRho.findFactor
      (n - 1) params fuel with
  | none => simp only [hfind, Option.map_none, reduceCtorEq] at h
  | some factor =>
    simp only [hfind, Option.map_some] at h
    have hp := PseudoPrime.NumberTheory.Factorization.PollardRho.findFactor_sound hfind
    change 1 < factor ∧ factor < n - 1 ∧ factor ∣ n - 1 at hp
    have heq : (factor, (n - 1) / factor) = (d, r) := Option.some.inj h
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    have hmul := Nat.mul_div_cancel' hp.2.2
    have hrpos : 0 < (n - 1) / factor := by
      by_contra hr
      have hz : (n - 1) / factor = 0 := Nat.eq_zero_of_not_pos hr
      rw [hz, mul_zero] at hmul
      exact (Nat.ne_of_gt
        (Nat.lt_trans Nat.zero_lt_one (lt_trans hp.1 hp.2.1))) hmul.symm
    have hrne : (n - 1) / factor ≠ 1 := by
      intro hr
      rw [hr, mul_one] at hmul
      exact (Nat.ne_of_lt hp.2.1) hmul
    exact ⟨hp.1,
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨Nat.ne_of_gt hrpos, hrne⟩,
      hmul⟩

/-- Turn a rho split into BLS partial factorization data when it already splits into
two distinct primes. Composite split parts are left unclassified and yield `none`.
The construction does not assert that the square-root bound holds. -/
def partialFactorizationOfPrimeSplit (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) :
    Option PartialFactorizationData :=
  match findNMinusOneFactor n params fuel with
  | none => none
  | some (d, r) =>
    if Nat.Prime d ∧ Nat.Prime r ∧ d ≠ r then some ⟨[(d, 1), (r, 1)], 1⟩ else none

/-- A prime split accepted by `partialFactorizationOfPrimeSplit` gives valid BLS factor data.
This supplies a consumer for rho's factor hint without trusting a potentially composite factor. -/
theorem partialFactorizationOfPrimeSplit_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData}
    (h : partialFactorizationOfPrimeSplit n params fuel = some data) :
    ValidPartialFactorization n data := by
  unfold partialFactorizationOfPrimeSplit at h
  cases hsplit : findNMinusOneFactor n params fuel with
  | none => simp only [hsplit, reduceCtorEq] at h
  | some pair =>
    rcases pair with ⟨d, r⟩
    simp only [hsplit] at h
    split at h
    · rename_i hprime
      have hdata : data = ⟨[(d, 1), (r, 1)], 1⟩ := Option.some.inj h.symm
      subst data
      have hsplitSound := findNMinusOneFactor_sound hsplit
      have hproduct :
          factorProduct [(d, 1), (r, 1)] = d * r := by
        rw [factorProduct_cons,
          factorProduct_cons]
        simp only [factorProduct, List.foldl_nil, pow_one, mul_one]
      apply (checkPartialFactorization_eq_true_iff
        n ⟨[(d, 1), (r, 1)], 1⟩).mpr
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hproduct]
        have hmul : 2 * 2 ≤ d * r :=
          Nat.mul_le_mul
            (Nat.succ_le_of_lt hsplitSound.1)
            (Nat.succ_le_of_lt hsplitSound.2.1)
        exact Nat.lt_of_lt_of_le (by decide : 1 < 2 * 2) hmul
      · rw [hproduct]
        simpa only [mul_one] using hsplitSound.2.2.symm
      · simp only [hprime.2.2, List.map_cons, List.map_nil, List.nodup_cons,
          List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
          List.nodup_nil, and_self]
      · intro qe hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with hmem | hmem
        · have heq : qe = (d, 1) := hmem
          subst qe
          exact ⟨hprime.1, Nat.zero_lt_one⟩
        · have heq : qe = (r, 1) := hmem
          subst qe
          exact ⟨hprime.2.1, Nat.zero_lt_one⟩
    · cases h

/-- Recursively split a natural number with a bounded rho schedule, returning only prime leaves.
The fuel is a maximum split depth: every internal node receives that many rho rounds. -/
abbrev primeFactorListFuel (params :
    NumberTheory.Factorization.PollardRho.Params) :
    ℕ → ℕ → Option (List ℕ) :=
  NumberTheory.Factorization.PollardRho.primeFactorListFuel exactPrimeLeafPolicy params

/-- On an even composite input above two, positive split depth factors by the immediate factor two
branch. This exposes the exact recursive result without unfolding any rho trajectory. -/
theorem primeFactorListFuel_even_eq_split {params : NumberTheory.Factorization.PollardRho.Params}
    {fuel n : ℕ} (hn : 2 < n) (hprime : ¬ Nat.Prime n) (heven : n % 2 = 0) :
    primeFactorListFuel params (fuel + 1) n =
      (match primeFactorListFuel params fuel 2,
          primeFactorListFuel params fuel (n / 2) with
        | some left, some right => some (left ++ right)
        | _, _ => none) := by
  exact NumberTheory.Factorization.PollardRho.primeFactorListFuel_even_eq_split hn hprime heven

/-- At zero split depth, success is exactly the prime input and its singleton factor list. -/
theorem primeFactorListFuel_zero_iff {params :
    NumberTheory.Factorization.PollardRho.Params} {n : ℕ} {factors : List ℕ} :
    primeFactorListFuel params 0 n = some factors ↔ Nat.Prime n ∧ factors = [n] := by
  exact NumberTheory.Factorization.PollardRho.primeFactorListFuel_zero_iff

/-- A prime input is returned immediately at every split-depth bound. -/
theorem primeFactorListFuel_of_prime {params :
    NumberTheory.Factorization.PollardRho.Params} {fuel n : ℕ}
    (hn : Nat.Prime n) : primeFactorListFuel params fuel n = some [n] := by
  exact NumberTheory.Factorization.PollardRho.primeFactorListFuel_of_accepts hn

/-- A successful recursive rho factorization consists of primes whose product is the input. -/
theorem primeFactorListFuel_sound {params :
    NumberTheory.Factorization.PollardRho.Params} {fuel n : ℕ} {factors : List ℕ}
    (hn : 1 < n) (h : primeFactorListFuel params fuel n = some factors) :
    (∀ p, p ∈ factors → Nat.Prime p) ∧ factors.prod = n := by
  exact NumberTheory.Factorization.PollardRho.primeFactorListFuel_sound hn h

/-- Apply recursive prime-leaf supply to `n - 1`, the integer factored by BLS. -/
def nMinusOnePrimeFactors (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) :
    Option (List ℕ) := primeFactorListFuel params fuel (n - 1)

/-- Every returned `n - 1` factor is prime and the returned list multiplies to `n - 1`. -/
theorem nMinusOnePrimeFactors_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {factors : List ℕ} (hn : 2 < n)
    (h : nMinusOnePrimeFactors n params fuel = some factors) :
    (∀ p, p ∈ factors → Nat.Prime p) ∧ factors.prod = n - 1 := by
  apply primeFactorListFuel_sound (Nat.lt_sub_iff_add_lt.mpr hn) h

/-- The fold-based BLS product agrees with the product of listed prime powers. -/
private theorem factorProduct_eq_list_prod (factors : List (ℕ × ℕ)) :
    factorProduct factors =
      (factors.map (fun qe => qe.1 ^ qe.2)).prod := by
  induction factors with
  | nil => simp only [factorProduct, List.map_nil, List.prod_nil, List.foldl_nil]
  | cons qe factors ih =>
    rw [factorProduct_cons,
      List.map_cons, List.prod_cons, ih]

/-- Aggregating repeated entries into prime powers preserves the list product. -/
theorem aggregatePrimeFactorList_product (factors : List ℕ) :
    factorProduct
      (NumberTheory.Factorization.aggregatePrimeFactorList factors) = factors.prod := by
  rw [factorProduct_eq_list_prod]
  exact NumberTheory.Factorization.aggregatePrimeFactorList_product factors

/-- Canonical prime-power data from the finite support of `Nat.factorization (n - 1)`.
This proof-oriented normalizer is noncomputable because `Finset.toList` chooses an ordering. -/
noncomputable def canonicalPartialFactorizationOfNMinusOne (n : ℕ) :
    PartialFactorizationData :=
  ⟨((n - 1).primeFactors.toList.map
      (fun q => (q, Nat.factorization (n - 1) q))), 1⟩

/-- The canonical factorization data has distinct prime keys and product `n - 1`. -/
theorem canonicalPartialFactorizationOfNMinusOne_valid {n : ℕ} (hn : 2 < n) :
    ValidPartialFactorization n
      (canonicalPartialFactorizationOfNMinusOne n) := by
  apply (checkPartialFactorization_eq_true_iff
    n (canonicalPartialFactorizationOfNMinusOne n)).mpr
  dsimp only [canonicalPartialFactorizationOfNMinusOne]
  let f := Nat.factorization (n - 1)
  have hn0 : n - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (Nat.lt_trans Nat.one_lt_two hn)
  have hproduct :
      factorProduct
        ((n - 1).primeFactors.toList.map (fun q => (q, f q))) = n - 1 := by
    rw [factorProduct_eq_list_prod]
    simp only [List.map_map, Function.comp_def]
    calc
      ((n - 1).primeFactors.toList.map (fun q => q ^ f q)).prod =
          (n - 1).primeFactors.prod (fun q => q ^ f q) := by rw [Finset.prod_map_toList]
      _ = f.prod (fun q e => q ^ e) := by
        symm
        exact Finsupp.prod_of_support_subset f (by rw [Nat.support_factorization])
          (fun q e => q ^ e) (by
            intro q hq
            exact Nat.pow_zero q)
      _ = n - 1 := by rw [Nat.prod_factorization_pow_eq_self hn0]
  have hkeys :
      (List.map Prod.fst ((n - 1).primeFactors.toList.map (fun q => (q, f q)))).Nodup := by
    have hmap :
        List.map Prod.fst ((n - 1).primeFactors.toList.map (fun q => (q, f q))) =
          (n - 1).primeFactors.toList := by
      simp only [List.map_map]
      simp only [Function.comp_def]
      exact List.map_id _
    rw [hmap]
    exact (n - 1).primeFactors.nodup_toList
  refine ⟨by
    rw [hproduct]
    exact Nat.lt_sub_iff_add_lt.mpr hn, ?_, hkeys, ?_⟩
  · rw [hproduct]
    simp only [mul_one]
  · intro qe hqe
    obtain ⟨q, hq, hpair⟩ := List.mem_map.mp hqe
    cases hpair
    have hqmem : q ∈ (n - 1).primeFactors := Finset.mem_toList.mp hq
    have hqsupport : q ∈ f.support := by
      rw [Nat.support_factorization]
      exact hqmem
    exact ⟨Nat.prime_of_mem_primeFactors hqmem,
      Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hqsupport)⟩

/-- Every `n > 2` has valid BLS data for the complete prime-power factorization of `n - 1`. -/
theorem exists_valid_partial_factorization_of_nMinusOne {n : ℕ} (hn : 2 < n) :
    ∃ data : PartialFactorizationData,
      ValidPartialFactorization n data :=
  ⟨canonicalPartialFactorizationOfNMinusOne n,
    canonicalPartialFactorizationOfNMinusOne_valid hn⟩

/-- Convert a complete prime factor list of `n - 1` to BLS partial data, combining repetitions
into prime exponents. The `none` case is exactly failure of the bounded recursive factor search. -/
def partialFactorizationOfNMinusOne (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) :
    Option PartialFactorizationData :=
  match nMinusOnePrimeFactors n params fuel with
  | none => none
  | some factors => some ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩

/-- Successful complete factor supply produces valid BLS partial factorization data. -/
theorem partialFactorizationOfNMinusOne_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData}
    (hn : 2 < n) (h : partialFactorizationOfNMinusOne n params fuel = some data) :
    ValidPartialFactorization n data := by
  unfold partialFactorizationOfNMinusOne at h
  cases hfactor : nMinusOnePrimeFactors n params fuel with
  | none => simp only [hfactor, reduceCtorEq] at h
  | some factors =>
    have hsome :
        some ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩ = some data := by
      simpa only [hfactor] using h
    have hdata : data = ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩ :=
      Option.some.inj hsome.symm
    subst data
    have hspec := nMinusOnePrimeFactors_sound hn hfactor
    have hproduct :
        factorProduct
          (NumberTheory.Factorization.aggregatePrimeFactorList factors) = n - 1 := by
      rw [aggregatePrimeFactorList_product, hspec.2]
    apply (checkPartialFactorization_eq_true_iff
      n ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩).mpr
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hproduct]
      exact Nat.lt_sub_iff_add_lt.mpr hn
    · rw [hproduct]
      simp only [mul_one]
    · change (NumberTheory.Factorization.aggregatePrimeFactorList factors).map Prod.fst |>.Nodup
      dsimp only [NumberTheory.Factorization.aggregatePrimeFactorList]
      have hmap :
          (factors.dedup.map (fun q => (q, factors.count q))).map Prod.fst =
            factors.dedup := by
        simp only [List.map_map, Function.comp_def]
        exact List.map_id _
      rw [hmap]
      exact List.nodup_dedup factors
    · intro qe hmem
      obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
      cases hqe
      have hqFactors : q ∈ factors := List.mem_dedup.mp hq
      exact ⟨hspec.1 q hqFactors,
        List.count_pos_iff.mpr hqFactors⟩

/-- Successful BLS factor supply here is complete: its prime-power product is exactly `n - 1`. -/
theorem partialFactorizationOfNMinusOne_fullProduct {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData}
    (hn : 2 < n) (h : partialFactorizationOfNMinusOne n params fuel = some data) :
    factorProduct data.factors = n - 1 := by
  unfold partialFactorizationOfNMinusOne at h
  cases hfactor : nMinusOnePrimeFactors n params fuel with
  | none => simp only [hfactor, reduceCtorEq] at h
  | some factors =>
    have hsome :
        some ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩ = some data := by
      simpa only [hfactor] using h
    have hdata : data = ⟨NumberTheory.Factorization.aggregatePrimeFactorList factors, 1⟩ :=
      Option.some.inj hsome.symm
    subst data
    rw [aggregatePrimeFactorList_product]
    exact (nMinusOnePrimeFactors_sound hn hfactor).2

/-- Search the supplied finite base list for one BLS witness per distinct prime factor.
Failure means at least one factor has no witness in this candidate list. -/
def findBLSWitnesses (n : ℕ) (factors : List (ℕ × ℕ)) (candidates : List ℕ) :
    Option (List (ℕ × ℕ)) :=
  match factors with
  | [] => some []
  | qe :: tail =>
    match findBLSWitness n qe.1 candidates,
        findBLSWitnesses n tail candidates with
    | some a, some witnesses => some ((qe.1, a) :: witnesses)
    | _, _ => none

/-- Successful witness collection has exactly the factor keys and every witness is valid. -/
theorem findBLSWitnesses_sound {n : ℕ} {factors : List (ℕ × ℕ)}
    {candidates : List ℕ} {witnesses : List (ℕ × ℕ)}
    (h : findBLSWitnesses n factors candidates = some witnesses) :
    witnesses.map Prod.fst = factors.map Prod.fst ∧
      ∀ qa, qa ∈ witnesses →
        IsBLSWitness n qa.1 qa.2 := by
  induction factors generalizing witnesses with
  | nil =>
    simp only [findBLSWitnesses, Option.some.injEq, List.nil_eq] at h
    subst witnesses
    exact ⟨rfl, by intro qa hqa; exact False.elim (List.not_mem_nil hqa)⟩
  | cons qe tail ih =>
    cases hbase : findBLSWitness
        n qe.1 candidates with
    | none => simp only [findBLSWitnesses, hbase, reduceCtorEq] at h
    | some a =>
      cases htail : findBLSWitnesses n tail candidates with
      | none => simp only [findBLSWitnesses, hbase, htail, reduceCtorEq] at h
      | some rest =>
        have hcons : (qe.1, a) :: rest = witnesses := by
          apply Option.some.inj
          simpa only [findBLSWitnesses, hbase, htail] using h
        subst witnesses
        have hvalid :=
          findBLSWitness_some_spec
            n qe.1 candidates a hbase
        have hrest := ih htail
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, hrest.1]
        · intro qa hqa
          rcases List.mem_cons.mp hqa with hhead | htail
          · cases hhead
            exact hvalid
          · exact hrest.2 qa htail

/-- The bounded witness collector succeeds exactly when every factor key has a witness among
the supplied bases. This separates the finite search's completeness hypothesis from its soundness.
-/
theorem findBLSWitnesses_isSome_iff {n : ℕ} {factors : List (ℕ × ℕ)}
    {candidates : List ℕ} :
    (findBLSWitnesses n factors candidates).isSome = true ↔
      ∀ qe, qe ∈ factors →
        ∃ a, a ∈ candidates ∧ IsBLSWitness n qe.1 a := by
  induction factors with
  | nil =>
    constructor
    · intro _ qe hqe
      exact False.elim (List.not_mem_nil hqe)
    · intro _
      rfl
  | cons qe tail ih =>
    cases hb : findBLSWitness n qe.1 candidates with
    | none =>
      constructor
      · simp only [findBLSWitnesses, hb, Option.isSome_none,
          Bool.false_eq_true, List.mem_cons, forall_eq_or_imp,
          Prod.forall, IsEmpty.forall_iff]
      · intro hcov
        obtain ⟨a, ha, hwa⟩ := hcov qe (List.mem_cons_self)
        have hs : (findBLSWitness n qe.1 candidates).isSome = true :=
          (findBLSWitness_isSome_iff n qe.1 candidates).mpr ⟨a, ha, hwa⟩
        rw [hb] at hs
        contradiction
    | some a =>
      cases ht : findBLSWitnesses n tail candidates with
      | none =>
        constructor
        · simp only [findBLSWitnesses, hb, ht, Option.isSome_none,
            Bool.false_eq_true, List.mem_cons, forall_eq_or_imp,
            Prod.forall, IsEmpty.forall_iff]
        · intro hcov
          have htailcov : ∀ qf, qf ∈ tail →
              ∃ b, b ∈ candidates ∧ IsBLSWitness n qf.1 b := by
            intro qf hmem
            exact hcov qf (List.mem_cons_of_mem qe hmem)
          have htailSome := ih.mpr htailcov
          rw [ht] at htailSome
          contradiction
      | some witnesses =>
        constructor
        · intro _ qf hmem
          rcases List.mem_cons.mp hmem with heq | hmem
          · cases heq
            have hmem : a ∈ candidates := by
              change List.find? (checkBLSWitness n qe.1) candidates = some a at hb
              exact List.mem_of_find?_eq_some hb
            exact ⟨a, hmem, findBLSWitness_some_spec n qe.1 candidates a hb⟩
          · exact ih.mp (by
              rw [ht]
              rfl) qf hmem
        · intro _
          simp only [findBLSWitnesses, hb, ht, Option.isSome_some]

/-- Every valid partial factorization of a prime `n ≥ 5` is covered by the exhaustive base list
`List.range n`, so the bounded witness collector succeeds. -/
theorem findBLSWitnesses_range_isSome {n : ℕ} (hn : Nat.Prime n) (hn5 : 5 ≤ n)
    (data : PartialFactorizationData) (hdata : ValidPartialFactorization n data) :
    (findBLSWitnesses n data.factors (List.range n)).isSome = true := by
  rw [findBLSWitnesses_isSome_iff]
  obtain ⟨a, ha, hvalid⟩ :=
    exists_common_blsWitness_for_valid_partialFactorization hn hn5 data hdata
  intro qe hmem
  exact ⟨a, ha, hvalid qe hmem⟩

/-- Attempt a complete bounded BLS certificate search from rho-supplied factors and bases.
It returns `none` if factorization or any individual witness search exhausts its bound. -/
def findSquareCertificate (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params)
    (factorFuel : ℕ) (bases : List ℕ) :
    Option SquareCertificate := do
  let data ← partialFactorizationOfNMinusOne n params factorFuel
  let witnesses ← findBLSWitnesses n data.factors bases
  pure ⟨n, data, witnesses⟩

/-- A bounded square-certificate search succeeds exactly when factor supply succeeds and every
factor key has a valid witness among the supplied bases. -/
theorem findSquareCertificate_isSome_iff {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ} {bases : List ℕ} :
    (findSquareCertificate n params fuel bases).isSome = true ↔
      ∃ data, partialFactorizationOfNMinusOne n params fuel = some data ∧
        ∀ qe, qe ∈ data.factors →
          ∃ a, a ∈ bases ∧ IsBLSWitness n qe.1 a := by
  unfold findSquareCertificate
  cases hd : partialFactorizationOfNMinusOne n params fuel with
  | none =>
    constructor
    · intro hsome
      simp only [Option.pure_def, Option.bind_eq_bind,
        Option.bind_none, Option.isSome_none,
        Bool.false_eq_true] at hsome
    · rintro ⟨data, hdata, _⟩
      simp only [reduceCtorEq] at hdata
  | some data =>
    cases hw : findBLSWitnesses n data.factors bases with
    | none =>
      constructor
      · intro hsome
        simp only [hw, Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, Option.bind_none,
          Option.isSome_none, Bool.false_eq_true] at hsome
      · rintro ⟨d, hdata, hcov⟩
        have hEq : data = d := Option.some.inj hdata
        subst d
        have hs := (findBLSWitnesses_isSome_iff).mpr hcov
        rw [hw] at hs
        contradiction
    | some witnesses =>
      constructor
      · intro _
        refine ⟨data, rfl, ?_⟩
        exact (findBLSWitnesses_isSome_iff).mp (by
          rw [hw]
          rfl)
      · rintro ⟨d, hdata, hcov⟩
        have hEq : data = d := Option.some.inj hdata
        subst d
        simp only [Option.pure_def, Option.bind_eq_bind,
          Option.bind_some, hw, Option.isSome_some]

/-- On a prime input `n ≥ 5`, any successful `n - 1` factor supply can be completed by the
exhaustive base list `List.range n` to a square-root BLS certificate. -/
theorem exists_findSquareCertificate_of_prime_factorSupply {n : ℕ}
    (hn : Nat.Prime n) (hn5 : 5 ≤ n) (params : NumberTheory.Factorization.PollardRho.Params)
    (fuel : ℕ) {data : PartialFactorizationData}
    (hdata : partialFactorizationOfNMinusOne n params fuel = some data) :
    ∃ certificate,
      findSquareCertificate n params fuel (List.range n) = some certificate := by
  have hn2 : 2 < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn5
  have hvalid : ValidPartialFactorization n data :=
    partialFactorizationOfNMinusOne_sound hn2 hdata
  have hwitnesses := findBLSWitnesses_range_isSome hn hn5 data hvalid
  cases hw : findBLSWitnesses n data.factors (List.range n) with
  | none =>
    simp only [hw, Option.isSome_none, Bool.false_eq_true] at hwitnesses
  | some witnesses =>
    refine ⟨⟨n, data, witnesses⟩, ?_⟩
    simp only [findSquareCertificate, hdata,
      Option.pure_def, Option.bind_eq_bind,
      Option.bind_some, hw]

/-- Any bounded certificate search success carries valid factorization and witness data. -/
theorem findSquareCertificate_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {factorFuel : ℕ} {bases : List ℕ}
    {certificate : SquareCertificate}
    (hn : 2 < n) (h : findSquareCertificate n params factorFuel bases = some certificate) :
    certificate.n = n ∧
      factorProduct
        certificate.factorization.factors = n - 1 ∧
      ValidPartialFactorization n
        certificate.factorization ∧
      ValidWitnesses n certificate.factorization
        certificate.witnesses := by
  unfold findSquareCertificate at h
  cases hdata : partialFactorizationOfNMinusOne n params factorFuel with
  | none =>
    simp only [hdata, Option.pure_def, Option.bind_eq_bind,
      Option.bind_none] at h
    cases h
  | some data =>
    cases hwitnesses : findBLSWitnesses n data.factors bases with
    | none =>
      simp only [hdata, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some,
        hwitnesses, Option.bind_none] at h
      cases h
    | some witnesses =>
      have hcert : (⟨n, data, witnesses⟩ :
          SquareCertificate) = certificate := by
        apply Option.some.inj
        simpa only [hdata, Option.pure_def,
          Option.bind_eq_bind, Option.bind_some,
          hwitnesses] using h
      have hfactor := partialFactorizationOfNMinusOne_sound hn hdata
      have hfull := partialFactorizationOfNMinusOne_fullProduct hn hdata
      have hwit := findBLSWitnesses_sound hwitnesses
      rw [← hcert]
      exact ⟨rfl, hfull, hfactor,
        (checkWitnesses_eq_true_iff
        n data witnesses).mpr hwit⟩

/-- A successful bounded search constructs a valid square-root BLS certificate and proves `n`
prime, provided the input is in the certificate's accepted range. -/
theorem prime_of_findSquareCertificate {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params}
    {factorFuel : ℕ} {bases : List ℕ}
    {certificate : SquareCertificate}
    (hn5 : 5 ≤ n)
    (h : findSquareCertificate n params factorFuel bases = some certificate) :
    Nat.Prime n := by
  have hn2 : 2 < n := Nat.lt_of_lt_of_le (by decide : 2 < 5) hn5
  obtain ⟨hcn, hfull, hfactor, hwitnesses⟩ := findSquareCertificate_sound hn2 h
  have hbound : n <
      factorProduct
        certificate.factorization.factors ^ 2 := by
    rw [hfull]
    have hx : 3 < n - 1 :=
      Nat.lt_sub_iff_add_lt.mpr (lt_of_lt_of_le (by decide : 4 < 5) hn5)
    have hpos : 0 < n - 1 :=
      Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 5) hn5)
    have hmul : 3 * (n - 1) < (n - 1) * (n - 1) :=
      Nat.mul_lt_mul_of_pos_right hx hpos
    have hle : n ≤ 3 * (n - 1) := by
      have hm : 1 ≤ n - 1 := Nat.le_of_lt (Nat.lt_sub_iff_add_lt.mpr
        (lt_of_lt_of_le (by decide : 2 < 5) hn5))
      calc
        n = (n - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.le_trans (by decide : 1 ≤ 5) hn5)).symm
        _ ≤ (n - 1) + (n - 1) := Nat.add_le_add_left hm (n - 1)
        _ = 2 * (n - 1) := (two_mul (n - 1)).symm
        _ ≤ 3 * (n - 1) := Nat.mul_le_mul_right (n - 1) (by decide : 2 ≤ 3)
    have hlt : n < (n - 1) * (n - 1) := lt_of_le_of_lt hle hmul
    simpa only [pow_two] using hlt
  have hn5c : 5 ≤ certificate.n := by
    rw [hcn]
    exact hn5
  have hboundc : certificate.n <
      factorProduct
        certificate.factorization.factors ^ 2 := by
    rw [hcn]
    exact hbound
  have hfactorc :
      ValidPartialFactorization certificate.n
        certificate.factorization := by
    change checkPartialFactorization
      certificate.n certificate.factorization = true
    rw [hcn]
    exact hfactor
  have hwitnessesc :
      ValidWitnesses certificate.n
        certificate.factorization certificate.witnesses := by
    change checkWitnesses
      certificate.n certificate.factorization certificate.witnesses = true
    rw [hcn]
    exact hwitnesses
  have hcheck :
      verifySquareCertificate certificate = true := by
    simp only [verifySquareCertificate,
      checkSquareCertificate,
      Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨hn5c, hboundc⟩, hfactorc⟩, hwitnessesc⟩
  have hprime :=
    prime_of_valid_square_certificate certificate hcheck
  exact hcn ▸ hprime

end PseudoPrime.PrimeTest.BLS
