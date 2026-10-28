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
public import PseudoPrime.Tests.PrimalityRegression.PrimalityRegression

/-!
# Factor-supply completeness boundaries

Kernel-checked counterexamples: increasing fuel alone does not make a fixed rho schedule complete.
This regression module is built separately from the public umbrella.
-/

-- This helper-only module keeps the regression lemmas private across the split.
set_option linter.privateModule false

@[expose] public section

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
