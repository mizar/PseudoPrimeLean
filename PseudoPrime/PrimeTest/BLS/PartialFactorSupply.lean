/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.Factorization.Partial
import PseudoPrime.NumberTheory.Factorization.PollardRho.Budget
import PseudoPrime.PrimeTest.BLS.FactorSupply
import PseudoPrime.PrimeTest.BLS.Cube
import PseudoPrime.PrimeTest.BLS.Extended
import PseudoPrime.NumberTheory.Factorization.PollardRho.Search

/-!
# Retained factor data for BLS
-/

namespace PseudoPrime.PrimeTest.BLS

/-- Recursively split with bounded rho attempts, retaining unresolved values in `remainder`. -/
abbrev partialPrimeFactorSupply (params : NumberTheory.Factorization.PollardRho.Params) :
    ℕ → ℕ → NumberTheory.Factorization.PartialPrimeFactorSupply :=
  NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply exactPrimeLeafPolicy params

/-- Every retained factor is prime, and the known factors times the residual cofactor equal the
input. The identity remains valid when rho stops at any unresolved composite leaf. -/
theorem partialPrimeFactorSupply_sound (params : NumberTheory.Factorization.PollardRho.Params)
    (fuel : ℕ) : ∀ n : ℕ,
    (∀ p, p ∈ (partialPrimeFactorSupply params fuel n).factors → Nat.Prime p) ∧
      (partialPrimeFactorSupply params fuel n).factors.prod *
        (partialPrimeFactorSupply params fuel n).remainder = n := by
  exact NumberTheory.Factorization.PollardRho.partialPrimeFactorSupply_sound
    exactPrimeLeafPolicy params fuel

/-- Execute a partial factor supply according to an explicit whole-tree budget. -/
abbrev partialPrimeFactorSupplyByTree (params : NumberTheory.Factorization.PollardRho.Params) :
    NumberTheory.Factorization.PollardRho.RhoBudgetTree → ℕ →
      NumberTheory.Factorization.PartialPrimeFactorSupply :=
  NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree exactPrimeLeafPolicy params

/-- A tree-guided supply retains only prime leaves and preserves the represented input exactly. -/
theorem partialPrimeFactorSupplyByTree_sound (params : NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) : ∀ n : ℕ,
    (∀ p, p ∈ (partialPrimeFactorSupplyByTree params tree n).factors → Nat.Prime p) ∧
      (partialPrimeFactorSupplyByTree params tree n).factors.prod *
        (partialPrimeFactorSupplyByTree params tree n).remainder = n := by
  exact NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTree_sound
    exactPrimeLeafPolicy params tree

/-- Count actual Floyd rounds used by a tree-guided partial factor supply. -/
abbrev partialPrimeFactorSupplyByTreeRounds (params :
    NumberTheory.Factorization.PollardRho.Params) :
    NumberTheory.Factorization.PollardRho.RhoBudgetTree → ℕ → ℕ :=
  NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTreeRounds
    exactPrimeLeafPolicy params

/-- Actual Floyd rounds at every reached node sum to no more than all allowances in the tree. -/
theorem partialPrimeFactorSupplyByTreeRounds_le (params :
    NumberTheory.Factorization.PollardRho.Params)
    (tree : NumberTheory.Factorization.PollardRho.RhoBudgetTree) (n : ℕ) :
    partialPrimeFactorSupplyByTreeRounds params tree n ≤ tree.totalFuel := by
  exact NumberTheory.Factorization.PollardRho.partialPrimeFactorSupplyByTreeRounds_le
    exactPrimeLeafPolicy params tree n

/-- Convert retained prime leaves to BLS prime-power data when their product exceeds one.
If no nontrivial certified part is known, return `none` instead of claiming a useful factorization.
-/
def partialFactorizationDataOfSupply (supply :
    NumberTheory.Factorization.PartialPrimeFactorSupply) :
    Option PartialFactorizationData :=
  let factors := NumberTheory.Factorization.aggregatePrimeFactorList supply.factors
  if 1 < factorProduct factors then some ⟨factors, supply.remainder⟩ else none

/-- A successful conversion preserves the input product and satisfies the BLS partial
factorization checker, provided the retained leaves are prime and the supply product is exact. -/
theorem partialFactorizationDataOfSupply_sound {supply :
    NumberTheory.Factorization.PartialPrimeFactorSupply} {n : ℕ}
    (hprimes : ∀ p, p ∈ supply.factors → Nat.Prime p)
    (hproduct : supply.factors.prod * supply.remainder = n - 1)
    {data : PartialFactorizationData}
    (h : partialFactorizationDataOfSupply supply = some data) :
    ValidPartialFactorization n data := by
  let factors := NumberTheory.Factorization.aggregatePrimeFactorList supply.factors
  have hbound : 1 < factorProduct factors := by
    have hif :
        (if 1 < factorProduct factors then
          some ⟨factors, supply.remainder⟩ else none) = some data := by
      exact h
    split at hif
    · assumption
    · cases hif
  have hdata : data = ⟨factors, supply.remainder⟩ := by
    have hif :
        (if 1 < factorProduct factors then
          some ⟨factors, supply.remainder⟩ else none) = some data := by
      exact h
    have hsome : some ⟨factors, supply.remainder⟩ = some data := by
      rw [ite_eq_left hbound] at hif
      exact hif
    exact Option.some.inj hsome.symm
  subst data
  apply (checkPartialFactorization_eq_true_iff n ⟨factors, supply.remainder⟩).mpr
  refine ⟨hbound, ?_, ?_, ?_⟩
  · calc
      n - 1 = supply.factors.prod * supply.remainder := hproduct.symm
      _ = factorProduct factors * supply.remainder := by
        rw [aggregatePrimeFactorList_product]
  · change (NumberTheory.Factorization.aggregatePrimeFactorList supply.factors).map Prod.fst
    |>.Nodup
    dsimp only [factors, NumberTheory.Factorization.aggregatePrimeFactorList]
    have hmap :
        (supply.factors.dedup.map fun q => (q, supply.factors.count q)).map Prod.fst =
          supply.factors.dedup := by
      simp only [List.map_map, Function.comp_def]
      exact List.map_id _
    rw [hmap]
    exact List.nodup_dedup _
  · intro qe hmem
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hmem
    cases hqe
    have hqFactors : q ∈ supply.factors := List.mem_dedup.mp hq
    exact ⟨hprimes q hqFactors, List.count_pos_iff.mpr hqFactors⟩

/-- Retain the prime factors discovered for `n - 1`, together with their unresolved cofactor. -/
def retainingPartialFactorizationOfNMinusOne (n : ℕ)
    (params : NumberTheory.Factorization.PollardRho.Params) (fuel : ℕ) :
    Option PartialFactorizationData :=
  partialFactorizationDataOfSupply (partialPrimeFactorSupply params fuel (n - 1))

/-- Any returned retained factorization passes the BLS data checker. -/
theorem retainingPartialFactorizationOfNMinusOne_sound {n : ℕ}
    {params : NumberTheory.Factorization.PollardRho.Params} {fuel : ℕ}
    {data : PartialFactorizationData}
    (h : retainingPartialFactorizationOfNMinusOne n params fuel = some data) :
    ValidPartialFactorization n data := by
  apply partialFactorizationDataOfSupply_sound
  · exact (partialPrimeFactorSupply_sound params fuel (n - 1)).1
  · exact (partialPrimeFactorSupply_sound params fuel (n - 1)).2
  · exact h

end PseudoPrime.PrimeTest.BLS
