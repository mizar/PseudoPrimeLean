/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteCorrelationDuality
public import Mathlib.Data.Fintype.BigOperators

/-! # Triple correlation moments of finite subsets of additive groups -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Count points x in S for which both x-a and x-b belong to S. The
natural-valued indicator product keeps the common first point explicit.
This is the three-point correlation used in weighted energy amplification. -/
def finiteTripleCorrelation {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G) (a b : G) :
    ℕ :=
  ∑ x : S, (if x.val - a ∈ S then 1 else 0) * (if x.val - b ∈ S then 1 else 0)

/-- The full squared mass of the three-point correlation equals the third
difference energy. Apply finite Gram duality to the reflected incidence
matrix, compute its row overlaps, and group pairs by difference. No bound
or symmetry hypothesis on S is needed. -/
theorem finite_triple_correlation_square_sum {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (S : Finset G) :
    (∑ a : G, ∑ b : G, finiteTripleCorrelation S a b ^ 2) =
      ∑ a : G, finiteDifferenceCorrelation S a ^ 3 := by
  have h := finite_gram_square_duality (fun (x : S) a ↦ if x.val - a ∈ S then 1 else 0)
  change
    (∑ a : G, ∑ b : G, finiteTripleCorrelation S a b ^ 2) =
      (∑ x : S,
        ∑ y : S,
          (∑ a : G, (if x.val - a ∈ S then 1 else 0 : ℕ) * (if y.val - a ∈ S then 1 else 0)) ^
            2) at h
  simp only [finite_reflected_incidence_overlap] at h
  rw [finite_subtype_pair_sum_eq_correlation S (fun a ↦ finiteDifferenceCorrelation S a ^ 2)] at h
  apply h.trans
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A weighted three-point sum has square bounded by third difference
energy times the squared weight mass. Apply finite Cauchy–Schwarz to all
ordered difference pairs and use the exact Gram identity. This is the
generic bridge from amplified triples to mixed third energy. -/
theorem finite_triple_correlation_weighted_square_le {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (S : Finset G) (w : G → G → ℕ) :
    (∑ a : G, ∑ b : G, w a b * finiteTripleCorrelation S a b) ^ 2 ≤
      (∑ a : G, finiteDifferenceCorrelation S a ^ 3) * ∑ a : G, ∑ b : G, w a b ^ 2 := by
  have h :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (G × G)) (fun z ↦ w z.1 z.2)
      (fun z ↦ finiteTripleCorrelation S z.1 z.2)
  simp only [Fintype.sum_prod_type, finite_triple_correlation_square_sum] at h
  exact h.trans_eq (Nat.mul_comm _ _)

end PseudoPrime.Analysis
