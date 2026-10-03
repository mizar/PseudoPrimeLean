/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.BLS.FactorCoverage
import PseudoPrime.PrimeTest.BLS.Search
import PseudoPrime.PrimeTest.BLS.Cube
import PseudoPrime.PrimeTest.BLS.Extended
import PseudoPrime.PrimeTest.APRCL.CyclotomicRing
import PseudoPrime.PrimeTest.APRCL.JacobiSum
import PseudoPrime.PrimeTest.APRCL.PairCheck
import Mathlib.Tactic.NormNum

/-!
# Factor-supply completeness boundaries

Kernel-checked counterexamples: increasing fuel alone does not make a fixed rho schedule complete.
This regression module is built separately from the public umbrella.
-/

namespace PseudoPrime.Tests.PrimalityRegression

/-- The executable cube-discriminant square test accepts the zero discriminant. -/
theorem cube_discriminant_squareTest_zero : PrimeTest.BLS.cubeDiscriminantIsSquare 0 1 = true := by
  decide

/-- The executable cube-discriminant square test rejects a negative discriminant. -/
theorem cube_discriminant_squareTest_negative :
    PrimeTest.BLS.cubeDiscriminantIsSquare 1 1 = false := by decide

/-- The complete cube-discriminant root search returns a certificate at zero. -/
theorem cube_discriminant_squareRoot_search_zero :
    PrimeTest.BLS.findCubeDiscriminantSquareRoot 0 1 = some 0 := by decide

/-- At `n = 3 = 2 * 1 + 1`, the cube quotient is zero while the discriminant is the square 1.
Thus a found root is not a compositeness result unless the positive-quotient hypothesis is known.
-/
theorem bls_cube_zero_quotient_prime_square_regression :
    PrimeTest.BLS.cubeQuotient 1 2 = 0 ∧
      PrimeTest.BLS.cubeDiscriminant 1 2 = 1 ∧
      PrimeTest.BLS.findCubeDiscriminantSquareRoot 1 2 = some 1 ∧ Nat.Prime 3 := by
  decide

/-- For `F=4` and `R=3`, the extended BLS Euclidean data have quotient zero, remainder three,
and discriminant nine. -/
theorem bls5_arithmetic_small_case :
    PrimeTest.BLS.bls5Quotient 3 4 = 0 ∧
      PrimeTest.BLS.bls5Remainder 3 4 = 3 ∧ PrimeTest.BLS.bls5Discriminant 3 4 = 9 := by
  decide

/-- The coprimality and even-factor hypotheses make the extended BLS remainder odd in a concrete
case. -/
theorem bls5_coprime_remainder_odd_small_case : Odd (PrimeTest.BLS.bls5Remainder 3 4) :=
  PrimeTest.BLS.bls5Remainder_odd_of_coprime (by decide : Even 4) (by decide : Nat.Coprime 4 3)

/-- The orbit of 2 under `x ↦ x² + 1` modulo 25 has Floyd gcds 1, 1, 25.
Thus every fuel budget fails, including budgets beyond the degenerate third comparison. -/
theorem rho_twentyFive_eq_none (fuel : ℕ) :
    NumberTheory.Factorization.PollardRho.findFactor 25 ⟨2, 1⟩ fuel = none := by
  have h1 : (-21 : ZMod 25).val = 4 := by decide
  have h2 : (-458304 : ZMod 25).val = 21 := by decide
  have h3 : (-44127887745906175987125 : ZMod 25).val = 0 := by decide
  rcases fuel with _ | _ | _ | fuel
  all_goals
    norm_num only [NumberTheory.Factorization.PollardRho.findFactor,
      NumberTheory.Factorization.PollardRho.search, NumberTheory.Factorization.PollardRho.step, h1,
      h2, h3, Nat.add_one_ne_zero, and_false, ite_eq_left, ite_eq_right]

/-- The composite leaf 25 cannot be certified by this fixed recursive rho schedule. -/
private theorem factor_twentyFive_eq_none (fuel : ℕ) :
    PrimeTest.BLS.primeFactorListFuel ⟨2, 1⟩ fuel 25 = none := by
  have hn : ¬Nat.Prime 25 := by decide
  cases fuel <;>
    simp only [PrimeTest.BLS.primeFactorListFuel,
      NumberTheory.Factorization.PollardRho.primeFactorListFuel]
  all_goals norm_num only [hn, rho_twentyFive_eq_none, ite_eq_left, ite_eq_right]

/-- A positive Pollard rho budget immediately detects the even factor of 50. -/
private theorem findFactor_fifty_eq_some_two (fuel : ℕ) :
    NumberTheory.Factorization.PollardRho.findFactor 50 ⟨2, 1⟩ (fuel + 1) = some 2 := by
  unfold NumberTheory.Factorization.PollardRho.findFactor
  rw [ite_eq_right (Nat.ne_of_gt (Nat.succ_pos fuel)), ite_eq_right (by decide : ¬50 ≤ 2),
    ite_eq_left (by decide : 50 % 2 = 0)]

/-- Splitting 50 into 2 and 25 still leaves the failed leaf 25 at every depth. -/
private theorem factor_fifty_eq_none (fuel : ℕ) :
    PrimeTest.BLS.primeFactorListFuel ⟨2, 1⟩ fuel 50 = none := by
  have hn : ¬Nat.Prime 50 := by decide
  cases fuel with
  | zero =>
    simp only [PrimeTest.BLS.primeFactorListFuel,
      NumberTheory.Factorization.PollardRho.primeFactorListFuel, hn, ite_false]
  | succ fuel =>
    simp only [PrimeTest.BLS.primeFactorListFuel,
      NumberTheory.Factorization.PollardRho.primeFactorListFuel, hn, ite_false,
      findFactor_fifty_eq_some_two fuel,
      PrimeTest.BLS.primeFactorListFuel_of_prime (by decide : Nat.Prime 2),
      factor_twentyFive_eq_none, Nat.reduceDiv]

/-- The failed branch propagates through the complete factorization request for 100. -/
private theorem factor_hundred_eq_none (fuel : ℕ) :
    PrimeTest.BLS.primeFactorListFuel ⟨2, 1⟩ fuel 100 = none := by
  have hn : ¬Nat.Prime 100 := by decide
  cases fuel with
  | zero =>
    simp only [PrimeTest.BLS.primeFactorListFuel,
      NumberTheory.Factorization.PollardRho.primeFactorListFuel, hn, ite_false]
  | succ
    fuel =>
    have hfind :
      NumberTheory.Factorization.PollardRho.findFactor 100 ⟨2, 1⟩ (fuel + 1) = some 2 := by
      unfold NumberTheory.Factorization.PollardRho.findFactor
      rw [ite_eq_right (Nat.ne_of_gt (Nat.succ_pos fuel)), ite_eq_right (by decide : ¬100 ≤ 2),
        ite_eq_left (by decide : 100 % 2 = 0)]
    simp only [PrimeTest.BLS.primeFactorListFuel,
      NumberTheory.Factorization.PollardRho.primeFactorListFuel, hn, ite_false, hfind,
      PrimeTest.BLS.primeFactorListFuel_of_prime (by decide : Nat.Prime 2), factor_fifty_eq_none,
      Nat.reduceDiv]

/-- Even the prime input 101 never yields a BLS certificate for this schedule.
The failure is independent of the candidate bases and split-depth budget. -/
theorem prime_certificate_search_can_always_fail (fuel : ℕ) (bases : List ℕ) :
    Nat.Prime 101 ∧ PrimeTest.BLS.findSquareCertificate 101 ⟨2, 1⟩ fuel bases = none := by
  refine ⟨by decide, ?_⟩
  simp only [PrimeTest.BLS.findSquareCertificate, PrimeTest.BLS.partialFactorizationOfNMinusOne,
    PrimeTest.BLS.nMinusOnePrimeFactors]
  rw [show 101 - 1 = (100 : ℕ) from rfl, factor_hundred_eq_none]
  change
    (do
        let data ← (none : Option PrimeTest.BLS.PartialFactorizationData)
        let witnesses ← PrimeTest.BLS.findBLSWitnesses 101 data.factors bases
        pure ⟨101, data, witnesses⟩) =
      none
  rfl

/-- The fixed-array APR-CL root-exponent search distinguishes identity, the root, and zero.
This kernel-checked regression preserves the `some 0`, `some 1`, and `none` API cases. -/
theorem aprcl_fixed_array_rootExponent_regression :
    PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 0) (by decide)
          (fun j => if j.val = 0 then 1 else 0) =
        some 0 ∧
      PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 0) (by decide)
          (fun j => if j.val = 1 then 1 else 0) =
        some 1 ∧
      PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 0) (by decide)
          (fun _ => 0) =
        none := by
  decide +kernel

/-- The least-exponent specification for the executable APR-CL array search returns
the zero exponent for the unit array, including the exact reduced-monomial certificate. -/
theorem aprcl_fixed_array_rootExponent_spec_regression :
    0 < PrimeTest.APRCL.primePowerIndex 3 0 ∧
      PrimeTest.APRCL.cyclotomicFixedArrayMonomialReduce 5 (p := 3) (k := 0) (by decide) 0 =
        PrimeTest.APRCL.cyclotomicFixedArrayOne 5 3 0 := by
  have hsearch :
    PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 0) (by decide)
        (PrimeTest.APRCL.cyclotomicFixedArrayOne 5 3 0) =
      some 0 := by
    decide +kernel
  have hspec :=
    (PrimeTest.APRCL.cyclotomicFixedArrayRootExponent_eq_some_iff 5 (by decide) (p := 3) (k := 0)
          (by decide) (PrimeTest.APRCL.cyclotomicFixedArrayOne 5 3 0) 0).mp
      hsearch
  exact ⟨hspec.1, hspec.2.1⟩

/-- A `none` result for the zero coefficient array excludes every reduced root monomial
in the bounded prime-power exponent range. -/
theorem aprcl_fixed_array_rootExponent_none_spec_regression :
    ∀ e,
      e < PrimeTest.APRCL.primePowerIndex 3 0 →
        PrimeTest.APRCL.cyclotomicFixedArrayMonomialReduce 5 (p := 3) (k := 0) (by decide) e ≠
          (fun _ : Fin 2 => 0) := by
  have hsearch :
    PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 0) (by decide)
        (fun _ : Fin 2 => 0) =
      none := by
    decide +kernel
  exact
    (PrimeTest.APRCL.cyclotomicFixedArrayRootExponent_eq_none_iff 5 (by decide) (p := 3) (k := 0)
          (by decide) (fun _ : Fin 2 => 0)).mp
      hsearch

/-- Monomial search covers the final negative block and retains the least exponent
when characteristic two makes distinct candidate powers coincide. Both checks use the kernel. -/
theorem aprcl_monomial_rootExponent_regression :
    PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 5 (p := 3) (k := 2) (by decide)
          (fun j => if j.val = 2 ∨ j.val = 11 then -1 else 0) =
        some 20 ∧
      PrimeTest.APRCL.cyclotomicFixedArrayRootExponent 2 (p := 2) (k := 0) (by decide)
          (fun _ => 1) =
        some 0 := by
  decide +kernel

/-- Squaring the degree-two cyclotomic root gives the coefficient vector `(-1, -1)`.
This checks the materialized square API on an explicit quotient-ring identity. -/
theorem aprcl_fixed_array_square_regression :
    PrimeTest.APRCL.cyclotomicFixedArraySquare 5 (p := 3) (k := 0) (by decide)
        (PrimeTest.APRCL.cyclotomicFixedArrayRoot 5 (p := 3) (k := 0) (by decide)) =
      (fun _ : Fin 2 => (-1 : ZMod 5)) := by
  funext j
  fin_cases j <;> decide +kernel

/-- The fast coefficient-array exponentiator returns the unit after a full root period.
This kernel-checked example covers the optimized power path on the degree-two quotient. -/
theorem aprcl_fixed_array_root_period_regression :
    PrimeTest.APRCL.cyclotomicFixedArrayPowBySquaring 5 (p := 3) (k := 0) (by decide)
        (PrimeTest.APRCL.cyclotomicFixedArrayRoot 5 (p := 3) (k := 0) (by decide))
        (PrimeTest.APRCL.primePowerIndex 3 0) =
      PrimeTest.APRCL.cyclotomicFixedArrayOne 5 3 0 := by
  decide +kernel

/-- A covered even split tree supplies `12 = 2^2 * 3`; the exhaustive BLS base search then
constructs a certificate for the prime 13. -/
theorem covered_factor_tree_builds_prime_certificate :
    ∃ certificate,
      PrimeTest.BLS.findSquareCertificate 13 ⟨2, 1⟩ 2 (List.range 13) = some certificate := by
  have hcoverage : PrimeTest.BLS.RhoFactorTreeCoverage ⟨2, 1⟩ 2 12 := by
    refine .even (by decide) (by decide) (.prime (by decide)) ?_
    refine .even (by decide) (by decide) (.prime (by decide)) (.prime (by decide))
  exact
    PrimeTest.BLS.exists_findSquareCertificate_of_coverage (by decide) (by decide) ⟨2, 1⟩ hcoverage

private theorem primeFactorListFuel_six_zero (params : NumberTheory.Factorization.PollardRho.Params)
    (h6 : ¬Nat.Prime 6) : PrimeTest.BLS.primeFactorListFuel params 0 6 = none := by
  simp only [PrimeTest.BLS.primeFactorListFuel,
    NumberTheory.Factorization.PollardRho.primeFactorListFuel, h6, ite_false]

private theorem primeFactorListFuel_twelve_one
    (params : NumberTheory.Factorization.PollardRho.Params) (h12 : ¬Nat.Prime 12) (h2 : Nat.Prime 2)
    (h6 : ¬Nat.Prime 6) : PrimeTest.BLS.primeFactorListFuel params 1 12 = none := by
  rw [PrimeTest.BLS.primeFactorListFuel_even_eq_split (by decide : 2 < 12) h12
      (by decide : 12 % 2 = 0)]
  rw [PrimeTest.BLS.primeFactorListFuel_of_prime h2]
  rw [primeFactorListFuel_six_zero params h6]

private theorem partialPrimeFactorSupply_zero_prime
    (params : NumberTheory.Factorization.PollardRho.Params) (h2 : Nat.Prime 2) :
    PrimeTest.BLS.partialPrimeFactorSupply params 0 2 = ⟨[2], 1⟩ := by
  simp only [PrimeTest.BLS.partialPrimeFactorSupply,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply, PrimeTest.exactPrimeLeafPolicy,
    h2, ite_true]

private theorem partialPrimeFactorSupply_zero_composite
    (params : NumberTheory.Factorization.PollardRho.Params) (h6 : ¬Nat.Prime 6) :
    PrimeTest.BLS.partialPrimeFactorSupply params 0 6 = ⟨[], 6⟩ := by
  simp only [PrimeTest.BLS.partialPrimeFactorSupply,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply, PrimeTest.exactPrimeLeafPolicy,
    h6, ite_false]

private theorem partialPrimeFactorSupply_twelve_one
    (params : NumberTheory.Factorization.PollardRho.Params) (h12 : ¬Nat.Prime 12) (h2 : Nat.Prime 2)
    (h6 : ¬Nat.Prime 6) : PrimeTest.BLS.partialPrimeFactorSupply params 1 12 = ⟨[2], 6⟩ := by
  rw [PrimeTest.BLS.partialPrimeFactorSupply,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply, PrimeTest.exactPrimeLeafPolicy,
    ite_eq_right h12,
    NumberTheory.Factorization.PollardRho.findFactor_eq_some_two_of_even params (by decide : 0 < 1)
      (by decide : 2 < 12) (by decide : 12 % 2 = 0)]
  simp only [partialPrimeFactorSupply_zero_prime params h2,
    partialPrimeFactorSupply_zero_composite params h6, List.append_nil, Nat.one_mul]

/-- At depth one, the complete supplier loses the prime factor found on the left when the right
branch remains composite. The partial supplier retains `2` and records `6` as its cofactor. -/
theorem partial_factor_supply_retains_known_leaf :
    PrimeTest.BLS.partialFactorizationOfNMinusOne 13 ⟨2, 1⟩ 1 = none ∧
      PrimeTest.BLS.retainingPartialFactorizationOfNMinusOne 13 ⟨2, 1⟩ 1 = some ⟨[(2, 1)], 6⟩ := by
  have h12 : ¬Nat.Prime 12 := by decide
  have h2 : Nat.Prime 2 := by decide
  have h6 : ¬Nat.Prime 6 := by decide
  constructor
  · rw [PrimeTest.BLS.partialFactorizationOfNMinusOne, PrimeTest.BLS.nMinusOnePrimeFactors,
      show 13 - 1 = 12 from rfl, primeFactorListFuel_twelve_one ⟨2, 1⟩ h12 h2 h6]
  · change
      PrimeTest.BLS.partialFactorizationDataOfSupply
          (PrimeTest.BLS.partialPrimeFactorSupply ⟨2, 1⟩ 1 (13 - 1)) =
        some ⟨[(2, 1)], 6⟩
    rw [show 13 - 1 = 12 from rfl, partialPrimeFactorSupply_twelve_one ⟨2, 1⟩ h12 h2 h6]
    decide

/-- The quotient-ring power checks accept a concrete witness and remain connected to the exact
natural-number witness specification. -/
theorem bls_zmod_power_witness_regression :
    PrimeTest.BLS.checkBLSWitness 13 2 2 = true ∧ PrimeTest.BLS.IsBLSWitness 13 2 2 := by
  constructor
  · decide
  · exact (PrimeTest.BLS.checkBLSWitness_eq_true_iff 13 2 2).mp (by decide)

end PseudoPrime.Tests.PrimalityRegression

namespace PseudoPrime.PrimeTest.BLS

/-- A prime input is returned as one prime leaf by every budget tree. -/
private theorem partialPrimeFactorSupplyByTree_of_prime
    (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) {n : ℕ} (hn : Nat.Prime n) :
    partialPrimeFactorSupplyByTree params tree n = ⟨[n], 1⟩ := by
  cases tree with
  | leaf =>
    rw [partialPrimeFactorSupplyByTree,
      NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree,
      PrimeTest.exactPrimeLeafPolicy, ite_eq_left hn]
  | split fuel left right =>
    rw [partialPrimeFactorSupplyByTree,
      NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree,
      PrimeTest.exactPrimeLeafPolicy, ite_eq_left hn]

/-- A positive split budget factors an even composite input above two through its factor two. -/
private theorem partialPrimeFactorSupplyByTree_even_split
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ)
    (left right : NumberTheory.Factorization.PollardRho.RhoBudgetTree) {n : ℕ} (hn : 2 < n)
    (hprime : ¬Nat.Prime n) (heven : n % 2 = 0) :
    partialPrimeFactorSupplyByTree params (.split (fuel + 1) left right) n =
      ⟨(partialPrimeFactorSupplyByTree params left 2).factors ++
          (partialPrimeFactorSupplyByTree params right (n / 2)).factors,
        (partialPrimeFactorSupplyByTree params left 2).remainder *
          (partialPrimeFactorSupplyByTree params right (n / 2)).remainder⟩ := by
  simp only [partialPrimeFactorSupplyByTree,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree,
    PrimeTest.exactPrimeLeafPolicy, ite_eq_right hprime,
    NumberTheory.Factorization.PollardRho.findFactor_eq_some_two_of_even params (Nat.succ_pos fuel)
        hn heven]

end PseudoPrime.PrimeTest.BLS

namespace PseudoPrime.Tests.PrimalityRegression

/-- An explicit two-node budget tree factors 12, stays within its total round allowance, and
constructs a verified BLS certificate for the prime 13. -/
theorem rho_budget_tree_builds_prime_certificate :
    ∃ certificate,
      PrimeTest.BLS.findSquareCertificateFromRoundBudget 13 ⟨2, 1⟩ 2 9 (List.range 13) =
          some certificate ∧
        PrimeTest.BLS.partialPrimeFactorSupplyByTreeRounds ⟨2, 1⟩
            (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9) 12 ≤
          9 := by
  let tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree :=
    .split 3 (.split 1 .leaf .leaf) (.split 1 .leaf .leaf)
  have htree : NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9 = tree := by decide
  let data : PrimeTest.BLS.PartialFactorizationData := ⟨[(2, 2), (3, 1)], 1⟩
  have h12 : ¬Nat.Prime 12 := by decide
  have h2 : Nat.Prime 2 := by decide
  have h6 : ¬Nat.Prime 6 := by decide
  have h3 : Nat.Prime 3 := by decide
  have heven12 : 12 % 2 = 0 := by decide
  have heven6 : 6 % 2 = 0 := by decide
  have hsupply : PrimeTest.BLS.partialPrimeFactorSupplyByTree ⟨2, 1⟩ tree 12 = ⟨[2, 2, 3], 1⟩ := by
    rw [PrimeTest.BLS.partialPrimeFactorSupplyByTree_even_split ⟨2, 1⟩ 2 _ _ (by decide) h12
        heven12]
    rw [PrimeTest.BLS.partialPrimeFactorSupplyByTree_of_prime ⟨2, 1⟩ _ h2]
    rw [PrimeTest.BLS.partialPrimeFactorSupplyByTree_even_split ⟨2, 1⟩ 0 _ _ (by decide) h6 heven6]
    rw [PrimeTest.BLS.partialPrimeFactorSupplyByTree_of_prime ⟨2, 1⟩ _ h2]
    rw [PrimeTest.BLS.partialPrimeFactorSupplyByTree_of_prime ⟨2, 1⟩ _ h3]
    rfl
  have hdata :
    PrimeTest.BLS.retainingPartialFactorizationOfNMinusOneByTree 13 ⟨2, 1⟩ tree = some data := by
    have haggregate :
      NumberTheory.Factorization.aggregatePrimeFactorList [2, 2, 3] = [(2, 2), (3, 1)] := by decide
    have hbound : 1 < PrimeTest.BLS.factorProduct [(2, 2), (3, 1)] := by decide
    simp only [data, PrimeTest.BLS.retainingPartialFactorizationOfNMinusOneByTree,
      PrimeTest.BLS.partialFactorizationDataOfSupply, hsupply, haggregate, hbound, ite_true]
  have hvalid := PrimeTest.BLS.retainingPartialFactorizationOfNMinusOneByTree_sound hdata
  have hcoverage :
    ∀ qe, qe ∈ data.factors → ∃ a, a ∈ List.range 13 ∧ PrimeTest.BLS.IsBLSWitness 13 qe.1 a := by
    have hsome :=
      PrimeTest.BLS.findBLSWitnesses_range_isSome (n := 13) (by decide) (by decide) data hvalid
    intro qe hmem
    exact (PrimeTest.BLS.findBLSWitnesses_isSome_iff.mp hsome) qe hmem
  have hbound : 13 < PrimeTest.BLS.factorProduct data.factors ^ 2 := by decide +kernel
  obtain ⟨certificate, hcertificate⟩ :=
    PrimeTest.BLS.exists_findSquareCertificateFromBudgetTree_of_coverage (by decide) hdata hbound
      hcoverage
  refine ⟨certificate, ?_, ?_⟩
  · rw [PrimeTest.BLS.findSquareCertificateFromRoundBudget, htree]
    exact hcertificate
  · have hrounds := PrimeTest.BLS.partialPrimeFactorSupplyByTreeRounds_le ⟨2, 1⟩ tree 12
    rw [← htree] at hrounds
    exact
      Nat.le_trans hrounds
        (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree_totalFuel_le 2 9)

/-- The certificate found by the covered budget-tree example makes the proof-carrying bounded
BLS entry return its prime branch for the original input 13. -/
theorem rho_budget_tree_bls_result_prime_branch :
    ∃ certificate : PrimeTest.BLS.SquareCertificate,
      ∃ hp : Nat.Prime 13,
        PrimeTest.BLS.findSquareCertificateFromRoundBudget 13 ⟨2, 1⟩ 2 9 (List.range 13) =
            some certificate ∧
          PrimeTest.BLS.boundedBLSResult 13 ⟨2, 1⟩
              (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9) (List.range 13) 0 =
            .prime hp := by
  obtain ⟨certificate, hcertificate, _⟩ := rho_budget_tree_builds_prime_certificate
  have hp13 : Nat.Prime 13 := by decide
  have hinput : 1 < 13 := by decide
  refine ⟨certificate, hp13, hcertificate, ?_⟩
  exact
    PrimeTest.BLS.boundedBLSResult_prime_case ⟨2, 1⟩
      (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9) (List.range 13) 0 hinput
      hcertificate

/-- The global-round-budget result API also returns a proof-carrying prime
branch for the explicit covered input 13. -/
theorem rho_round_budget_result_prime_branch :
    ∃ hp : Nat.Prime 13,
      PrimeTest.BLS.boundedBLSResultFromRoundBudget 13 ⟨2, 1⟩ 2 9 (List.range 13) 0 =
        .prime hp := by
  obtain ⟨certificate, hcertificate, _⟩ := rho_budget_tree_builds_prime_certificate
  exact
    (PrimeTest.BLS.boundedBLSResultFromRoundBudget_prime_iff_certificate ⟨2, 1⟩ 2 9 (List.range 13)
          0 (by decide)).mpr
      ⟨certificate, hcertificate⟩

/-- With empty witness bases, the round-budget result uses the fallback factor
search to prove that the even input four is composite. -/
theorem round_budget_result_composite_small :
    ∃ hnot : ¬Nat.Prime 4,
      PrimeTest.BLS.boundedBLSResultFromRoundBudget 4 ⟨2, 1⟩ 0 0 [] 1 = .composite hnot := by
  apply
    (PrimeTest.BLS.boundedBLSResultFromRoundBudget_composite_iff ⟨2, 1⟩ 0 0 [] 1 (by decide)).mpr
  refine ⟨?_, 2, ?_⟩
  · decide
  · exact
      NumberTheory.Factorization.PollardRho.findFactor_eq_some_two_of_even ⟨2, 1⟩ (by decide)
        (by decide) (by decide)

/-- With no witness base and no fallback factor fuel, the same input remains
unknown; finite search failure is not reported as compositeness. -/
theorem round_budget_result_unknown_small :
    PrimeTest.BLS.boundedBLSResultFromRoundBudget 4 ⟨2, 1⟩ 0 0 [] 0 = .unknown := by
  apply (PrimeTest.BLS.boundedBLSResultFromRoundBudget_unknown_iff ⟨2, 1⟩ 0 0 [] 0 (by decide)).mpr
  constructor
  · decide
  · decide

/-- The same budget-tree result exposes its successful prime branch and the cube criterion for
the original input, using the exact certificate consumed by the result entry. -/
theorem rho_budget_tree_bls_result_prime_branch_with_cube_criterion :
    ∃ certificate : PrimeTest.BLS.SquareCertificate,
      ∃ hp : Nat.Prime 13,
        PrimeTest.BLS.findSquareCertificateFromRoundBudget 13 ⟨2, 1⟩ 2 9 (List.range 13) =
            some certificate ∧
          PrimeTest.BLS.boundedBLSResult 13 ⟨2, 1⟩
              (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9) (List.range 13) 0 =
            .prime hp ∧
          (Nat.Prime 13 ↔
            PrimeTest.BLS.cubeQuotient certificate.factorization.cofactor
                  (PrimeTest.BLS.factorProduct certificate.factorization.factors) =
                0 ∨
              PrimeTest.BLS.findCubeDiscriminantSquareRoot certificate.factorization.cofactor
                  (PrimeTest.BLS.factorProduct certificate.factorization.factors) =
                none) := by
  obtain ⟨certificate, hp, hcertificate, hresult⟩ := rho_budget_tree_bls_result_prime_branch
  have hcriterion :=
    (PrimeTest.BLS.boundedBLSResult_prime_case_with_cubeCriterion ⟨2, 1⟩
        (NumberTheory.Factorization.PollardRho.balancedRhoBudgetTree 2 9) (List.range 13) 0
        (by decide) hcertificate).2
  have hnumber :=
    PrimeTest.BLS.certificate_n_eq_input_of_findSquareCertificateFromBudgetTree hcertificate
  rw [hnumber] at hcriterion
  exact ⟨certificate, hp, hcertificate, hresult, hcriterion⟩

/-- The even-input factor shortcut supplies a proper factor, which the bounded BLS entry returns
as its proof-carrying composite branch when the empty base list cannot produce a certificate. -/
theorem rho_even_input_bls_result_composite_branch :
    ∃ hcomposite : ¬Nat.Prime 4,
      PrimeTest.BLS.boundedBLSResult 4 ⟨2, 1⟩ .leaf [] 1 = .composite hcomposite := by
  have hcomposite : ¬Nat.Prime 4 := by decide
  have hinput : 1 < 4 := by decide
  have hcertificate :
    PrimeTest.BLS.findSquareCertificateFromBudgetTree 4 ⟨2, 1⟩ .leaf [] = none := by decide
  have hfuel : 0 < 1 := by decide
  have hlarge : 2 < 4 := by decide
  have heven : 4 % 2 = 0 := by decide
  have hfactor : NumberTheory.Factorization.PollardRho.findFactor 4 ⟨2, 1⟩ 1 = some 2 :=
    NumberTheory.Factorization.PollardRho.findFactor_eq_some_two_of_even ⟨2, 1⟩ hfuel hlarge heven
  refine ⟨hcomposite, ?_⟩
  exact PrimeTest.BLS.boundedBLSResult_composite_case ⟨2, 1⟩ .leaf [] 1 hinput hcertificate hfactor

/-- For `n = 15`, the extended BLS quotient and discriminant identify the factors `3` and `5`,
and the positive-quotient square criterion returns a compositeness proof. -/
theorem bls5_square_discriminant_composite_small_case : ¬Nat.Prime 15 := by
  exact
    PrimeTest.BLS.bls5NotPrime_of_positive_quotient_and_discriminant_square (by decide : 1 < 15)
      (by decide : 0 < 2) (by decide : 15 = 2 * 7 + 1)
      (by decide : 0 < PrimeTest.BLS.bls5Quotient 7 2) 1
      (by decide : PrimeTest.BLS.bls5Discriminant 7 2 = (1 : ℤ) ^ 2)

/-- The same square discriminant reaches the proof-carrying composite result for `15`. -/
theorem bls5_discriminant_result_composite_small :
    ∃ hcomp : ¬Nat.Prime 15,
      PrimeTest.BLS.bls5DiscriminantResult (by decide : 1 < 15) (by decide : 0 < 2)
          (by decide : 15 = 2 * 7 + 1) (by decide : 0 < PrimeTest.BLS.bls5Quotient 7 2) =
        .composite hcomp := by
  exact
    PrimeTest.BLS.bls5DiscriminantResult_composite_of_some (z := 1) (by decide) (by decide)
      (by decide) (by decide) (by decide +kernel)

/-- With one unit of factor fuel, retained `3 · 9` for `28` reaches the combined
BLS5 search's proof-carrying composite branch. -/
theorem bls5_combined_search_composite_28 :
    ∃ hcomp : ¬Nat.Prime 28,
      PrimeTest.BLS.boundedBLS5SearchWithComposite 28 ⟨2, 1⟩ 1 [] = .composite hcomp := by
  exact
    PrimeTest.BLS.boundedBLS5SearchWithComposite_composite_of_root ⟨2, 1⟩ 1 [] (data :=
      ⟨[(3, 1)], 9⟩) (z := 1) (by decide) (by decide +kernel) (by decide) (by decide +kernel)

/-- Zero factor fuel leaves the same bounded input undecided. -/
theorem bls5_combined_search_unknown_fuel_zero :
    PrimeTest.BLS.boundedBLS5SearchWithComposite 28 ⟨2, 1⟩ 0 [] = .unknown := by
  exact
    PrimeTest.BLS.boundedBLS5SearchWithComposite_unknown_of_no_factor ⟨2, 1⟩ 0 [] (by decide)
      (by decide +kernel)

/-- At `n=13`, retained `F=2,R=6` gives a positive BLS5 quotient but a
negative discriminant, so the combined search remains unknown. -/
theorem bls5_combined_search_unknown_nonsquare_13 :
    PrimeTest.BLS.boundedBLS5SearchWithComposite 13 ⟨2, 1⟩ 1 [] = .unknown := by
  exact
    PrimeTest.BLS.boundedBLS5SearchWithComposite_unknown_of_root_none ⟨2, 1⟩ 1 [] (data :=
      ⟨[(2, 1)], 6⟩) (by decide) (by decide +kernel) (by decide +kernel) (by decide)
      (by decide +kernel)

/-- At `n=7`, full retained factorization makes the BLS5 quotient zero;
without a witness base, the combined search remains unknown. -/
theorem bls5_combined_search_unknown_zero_7 :
    PrimeTest.BLS.boundedBLS5SearchWithComposite 7 ⟨2, 1⟩ 1 [] = .unknown := by
  exact
    PrimeTest.BLS.boundedBLS5SearchWithComposite_unknown_of_zero ⟨2, 1⟩ 1 [] (data :=
      ⟨[(2, 1), (3, 1)], 1⟩) (by decide) (by decide +kernel) (by decide +kernel) (by decide)

/-- A small accepted BLS5 certificate reuses the factor `2^2` and its base-2 witness to certify
the prime input `13`. -/
theorem bls5_verified_certificate_prime_small_case : Nat.Prime 13 := by
  apply
    PrimeTest.BLS.prime_of_valid_bls5_certificate
      (⟨13, ⟨[(2, 2)], 3⟩, [(2, 2)], 3⟩ : PrimeTest.BLS.BLS5Certificate)
  decide

/-- The accepted small BLS5 certificate is consumed by the shared result API as a prime result. -/
theorem bls5_certificate_result_small_case :
    PrimeTest.BLS.boundedBLS5Result 13
        (some (⟨13, ⟨[(2, 2)], 3⟩, [(2, 2)], 3⟩ : PrimeTest.BLS.BLS5Certificate)) =
      .prime
        (PrimeTest.BLS.prime_of_valid_bls5_certificate ⟨13, ⟨[(2, 2)], 3⟩, [(2, 2)], 3⟩
          (by decide)) := by
  exact
    PrimeTest.BLS.boundedBLS5Result_prime_case ⟨13, ⟨[(2, 2)], 3⟩, [(2, 2)], 3⟩ (by decide) rfl
      (by decide)

set_option maxRecDepth 660 in
/-- The retained factor `F = 4` certifies `101` using BLS5 with unresolved cofactor `25`.
The witness is checked by kernel reduction, including the nonsquare discriminant condition. -/
theorem bls5_verified_certificate_prime_extended_case : Nat.Prime 101 := by
  apply
    PrimeTest.BLS.prime_of_valid_bls5_certificate
      (⟨101, ⟨[(2, 2)], 25⟩, [(2, 2)], 25⟩ : PrimeTest.BLS.BLS5Certificate)
  decide

/-- The retained factor in the extended example does not satisfy the square-root bound. -/
theorem bls5_extended_case_outside_square_bound : ¬101 < 4 ^ 2 := by decide

/-- Replacing the valid base by `1` makes the extended certificate fail its witness check. -/
theorem bls5_extended_case_rejects_bad_witness :
    PrimeTest.BLS.checkBLS5Certificate ⟨101, ⟨[(2, 2)], 25⟩, [(2, 1)], 25⟩ = false := by decide

set_option maxRecDepth 660 in
/-- The retained factor `F = 4`, unresolved cofactor `R = 25`, and base `2`
satisfy the conditional BLS5 search contract and reach the prime result for `101`. -/
theorem bls5_bounded_search_prime_of_coverage :
    ∃ hprime : Nat.Prime 101, PrimeTest.BLS.boundedBLS5Search 101 ⟨2, 1⟩ 2 [2] = .prime hprime := by
  have hdata :
    PrimeTest.BLS.retainingPartialFactorizationOfNMinusOne 101 ⟨2, 1⟩ 2 = some ⟨[(2, 2)], 25⟩ := by
    decide +kernel
  have hcoverage :
    ∀ qe,
      qe ∈ ([(2, 2)] : List (ℕ × ℕ)) → ∃ a, a ∈ [2] ∧ PrimeTest.BLS.IsBLSWitness 101 qe.1 a := by
    intro qe hqe
    have heq : qe = (2, 2) := List.mem_singleton.mp hqe
    cases heq
    exact ⟨2, by decide, (PrimeTest.BLS.checkBLSWitness_eq_true_iff 101 2 2).mp (by decide +kernel)⟩
  exact
    PrimeTest.BLS.exists_boundedBLS5Search_prime_of_coverage (by decide) hdata (by decide)
      (by decide) (by decide) (by decide) hcoverage

set_option maxRecDepth 660 in
/-- The combined BLS5 search retains the accepted prime certificate for `101`. -/
theorem bls5_combined_search_prime_101 :
    ∃ hprime : Nat.Prime 101,
      PrimeTest.BLS.boundedBLS5SearchWithComposite 101 ⟨2, 1⟩ 2 [2] = .prime hprime := by
  have hcert :
    PrimeTest.BLS.findBLS5Certificate 101 ⟨2, 1⟩ 2 [2] =
      some ⟨101, ⟨[(2, 2)], 25⟩, [(2, 2)], 25⟩ := by
    decide +kernel
  exact
    ⟨(PrimeTest.BLS.findBLS5Certificate_some_spec hcert).1 ▸
        PrimeTest.BLS.prime_of_valid_bls5_certificate ⟨101, ⟨[(2, 2)], 25⟩, [(2, 2)], 25⟩
          (PrimeTest.BLS.findBLS5Certificate_some_spec hcert).2,
      PrimeTest.BLS.boundedBLS5SearchWithComposite_prime_case ⟨2, 1⟩ 2 [2] (by decide) hcert⟩

/-- For the prime input `7`, the typed low two-adic pair matches exponent zero,
while it does not establish `L₂`. A missing flag is not a failed main test. -/
theorem aprcl_low_main_pass_without_lp :
    (PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)).check.mainExponent =
        some 0 ∧
      (PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide)
            (by decide)).check.flagExponent =
        none ∧
      Nat.Prime 7 := by
  decide

/-- The finite pair-list interface likewise keeps the successful main test
separate from the absent arithmetic flag guard on the prime input `7`. -/
theorem aprcl_low_list_main_pass_without_flag :
    PrimeTest.APRCL.APRCLPairInput.allMainPassed
          [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)] =
        true ∧
      PrimeTest.APRCL.APRCLPairInput.anyFlagGuardMet
          [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)] =
        false ∧
      Nat.Prime 7 := by
  decide

/-- A supplied low two-adic pair covers its own `(p,k,q)` key and passes the main test. -/
theorem aprcl_low_required_key_pass :
    PrimeTest.APRCL.APRCLPairInput.checkRequired
        [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)] [(2, 0, 3)] =
      true := by
  decide

/-- Requiring the absent four-period key rejects the same finite pair list. -/
theorem aprcl_missing_key_rejected :
    PrimeTest.APRCL.APRCLPairInput.checkRequired
        [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)] [(2, 1, 3)] =
      false := by
  decide

/-- Parameter `t=2` requires exactly the low two-adic pair for auxiliary prime `3`. -/
theorem aprcl_parameter_keys_t2 : PrimeTest.APRCL.requiredPairKeys 2 = [(2, 0, 3)] := by
  decide +kernel

/-- The low two-adic input for `n=7` passes the parameter-derived main-test list. -/
theorem aprcl_parameter_check_t2 :
    PrimeTest.APRCL.APRCLPairInput.checkRequired
        [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)]
        (PrimeTest.APRCL.requiredPairKeys 2) =
      true := by
  rw [aprcl_parameter_keys_t2]
  decide

/-- At `n=7`, the odd-prime initial condition retains `L₃` candidate data even
after a mismatched pair, while the initial tag cannot establish `L₂`. -/
theorem aprcl_lp_initial_and_failed_pair_7 :
    PrimeTest.APRCL.LpEvidenceData.collect 6 3
          [PrimeTest.APRCL.LpEvidenceData.pair
              (PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)),
            PrimeTest.APRCL.LpEvidenceData.initial] =
        some PrimeTest.APRCL.LpEvidenceData.initial ∧
      PrimeTest.APRCL.LpEvidenceData.collect 6 2
          [(PrimeTest.APRCL.LpEvidenceData.initial : PrimeTest.APRCL.LpEvidenceData 7)] =
        none := by
  constructor
  · rfl
  · rfl

/-- The low two-adic pair at `n=5` supplies both its required main test and
the arithmetic flag candidate for `t=2`. -/
theorem aprcl_pair_and_flag_5 :
    PrimeTest.APRCL.checkRequiredWithFlags 2
        [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 5) 3 (by decide) (by decide)]
        [PrimeTest.APRCL.LpEvidenceData.pair
            (PrimeTest.APRCL.APRCLPairInput.twoOne (n := 5) 3 (by decide) (by decide))] =
      true := by
  decide +kernel

/-- The same main test at `n=7` cannot pass the missing two-adic flag guard. -/
theorem aprcl_pair_without_flag_7 :
    PrimeTest.APRCL.checkRequiredWithFlags 2
        [PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide)]
        [PrimeTest.APRCL.LpEvidenceData.pair
            (PrimeTest.APRCL.APRCLPairInput.twoOne (n := 7) 3 (by decide) (by decide))] =
      false := by
  decide +kernel

/-- The combined finite check rejects parameter zero before inspecting lists. -/
theorem aprcl_pair_and_flag_rejects_zero :
    PrimeTest.APRCL.checkRequiredWithFlags 0 ([] : List (PrimeTest.APRCL.APRCLPairInput 5))
        ([] : List (PrimeTest.APRCL.LpEvidenceData 5)) =
      false := by
  decide

/-- The backend index is one less than the mathematical two-adic valuation. -/
theorem aprcl_two_adic_backend_periods :
    PrimeTest.APRCL.primePowerIndex 2 0 = 2 ∧
      PrimeTest.APRCL.primePowerIndex 2 1 = 4 ∧ PrimeTest.APRCL.primePowerIndex 2 2 = 8 := by
  decide

/-- At period eight, the inverse action at index three multiplies the character exponent by
three; an unchanged Jacobi datum would miss this conjugation. -/
theorem aprcl_inverse_conjugate_exponent_three (datum : PrimeTest.APRCL.APRCLJacobiDatum 2 2) :
    (datum.inverseConjugate 3).exponent₁ = datum.exponent₁ * 3 := by
  change datum.exponent₁ * ((3 : ZMod 8)⁻¹).val = datum.exponent₁ * 3
  rw [ZMod.inv_eq_of_mul_eq_one 8 3 3 (by decide)]
  rfl

/-- A cube-root certificate for `17` uses the retained factor `F = 4`, cofactor `R = 4`,
and a base-3 witness for the factor `2`. The checker proves primality independently of the
square-root certificate. -/
theorem cube_verified_certificate_prime_beyond_square_bound : Nat.Prime 17 := by
  apply PrimeTest.BLS.prime_of_valid_cube_certificate ⟨17, ⟨[(2, 2)], 4⟩, [(2, 3)]⟩
  decide

/-- The preceding cube-root certificate lies beyond the square-root bound. -/
theorem cube_verified_certificate_square_bound_fails : ¬17 < 4 ^ 2 := by decide

/-- The bounded factor and witness search finds the same independent cube-root certificate
for `17`, so its result API returns a primality proof beyond the square-root bound. -/
theorem cube_bounded_search_prime_beyond_square_bound :
    ∃ h : Nat.Prime 17, PrimeTest.BLS.boundedCubeSearch 17 ⟨2, 1⟩ 2 [3] = .prime h := by
  have hdata :
    PrimeTest.BLS.retainingPartialFactorizationOfNMinusOne 17 ⟨2, 1⟩ 2 = some ⟨[(2, 2)], 4⟩ := by
    decide +kernel
  have hcoverage :
    ∀ qe, qe ∈ ([(2, 2)] : List (ℕ × ℕ)) → ∃ a, a ∈ [3] ∧ PrimeTest.BLS.IsBLSWitness 17 qe.1 a := by
    intro qe hqe
    have heq : qe = (2, 2) := List.mem_singleton.mp hqe
    cases heq
    exact ⟨3, by decide, (PrimeTest.BLS.checkBLSWitness_eq_true_iff 17 2 3).mp (by decide)⟩
  exact
    PrimeTest.BLS.exists_boundedCubeSearch_prime_of_coverage (by decide) hdata (by decide)
      (by decide) hcoverage

end PseudoPrime.Tests.PrimalityRegression
