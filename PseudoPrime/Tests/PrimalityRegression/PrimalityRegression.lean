/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

-- Kernel computation of APR-CL keys needs mergeSort's recursive implementation.
import all Init.Data.List.Sort.Basic

public import PseudoPrime.PrimeTest.BLS.FactorCoverage
public import PseudoPrime.PrimeTest.BLS.Search
public import PseudoPrime.PrimeTest.BLS.Cube
public import PseudoPrime.PrimeTest.BLS.Extended
public import PseudoPrime.PrimeTest.APRCL.CyclotomicRing
public import PseudoPrime.PrimeTest.APRCL.JacobiSum
public import PseudoPrime.PrimeTest.APRCL.PairCheck
public import Mathlib.Tactic.NormNum

/-!
# Factor-supply completeness boundaries

Kernel-checked counterexamples: increasing fuel alone does not make a fixed rho schedule complete.
This regression module is built separately from the public umbrella.
-/

@[expose] public section

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

/-- With six known composite, zero split depth cannot produce a complete prime-factor list.
Unfold the complete supplier to isolate the unresolved right branch of the twelve regression. -/
private theorem primeFactorListFuel_six_zero (params : NumberTheory.Factorization.PollardRho.Params)
    (h6 : ¬Nat.Prime 6) : PrimeTest.BLS.primeFactorListFuel params 0 6 = none := by
  simp only [PrimeTest.BLS.primeFactorListFuel,
    NumberTheory.Factorization.PollardRho.primeFactorListFuel, h6, ite_false]

/-- At depth one, complete factorization of twelve fails for any rho parameters.
Its even split certifies two but leaves six at depth zero; this supplies the failed complete
half of the retained-leaf regression. -/
private theorem primeFactorListFuel_twelve_one
    (params : NumberTheory.Factorization.PollardRho.Params) (h12 : ¬Nat.Prime 12) (h2 : Nat.Prime 2)
    (h6 : ¬Nat.Prime 6) : PrimeTest.BLS.primeFactorListFuel params 1 12 = none := by
  rw [PrimeTest.BLS.primeFactorListFuel_even_eq_split (by decide : 2 < 12) h12
      (by decide : 12 % 2 = 0)]
  rw [PrimeTest.BLS.primeFactorListFuel_of_prime h2]
  rw [primeFactorListFuel_six_zero params h6]

/-- The exact leaf policy certifies two even at zero split depth, returning `[2]` and cofactor one.
Unfold the prime branch for the retained-factor regression. -/
private theorem partialPrimeFactorSupply_zero_prime
    (params : NumberTheory.Factorization.PollardRho.Params) (h2 : Nat.Prime 2) :
    PrimeTest.BLS.partialPrimeFactorSupply params 0 2 = ⟨[2], 1⟩ := by
  simp only [PrimeTest.BLS.partialPrimeFactorSupply,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply, PrimeTest.exactPrimeLeafPolicy,
    h2, ite_true]

/-- At zero split depth, the partial supplier preserves the composite six as its entire cofactor.
Unfold the rejected-leaf branch; no certified factor is lost when a parent combines this result. -/
private theorem partialPrimeFactorSupply_zero_composite
    (params : NumberTheory.Factorization.PollardRho.Params) (h6 : ¬Nat.Prime 6) :
    PrimeTest.BLS.partialPrimeFactorSupply params 0 6 = ⟨[], 6⟩ := by
  simp only [PrimeTest.BLS.partialPrimeFactorSupply,
    NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply, PrimeTest.exactPrimeLeafPolicy,
    h6, ite_false]

/-- For any rho parameters, one even split of twelve retains factor two and cofactor six.
Use the factor-two shortcut and the two zero-depth child evaluations to establish the partial
half of the retained-leaf regression. -/
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
