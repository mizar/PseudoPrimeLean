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
public import PseudoPrime.PrimeTest.BLS.PrimalityRegression
import all PseudoPrime.PrimeTest.BLS.PrimalityRegression

/-!
# Factor-supply completeness boundaries

Kernel-checked counterexamples: increasing fuel alone does not make a fixed rho schedule complete.
This regression module is built separately from the public umbrella.
-/

@[expose] public section

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
