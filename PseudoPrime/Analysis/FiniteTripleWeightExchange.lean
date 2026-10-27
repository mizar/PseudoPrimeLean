/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteTripleCorrelations

/-! # Exact exchange between weighted triples and three-point correlations -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Sum a weight over differences from a fixed point x to a finite set S.
The involution y↦x-y gives the ambient sum with reflected support. This
is the one-variable change of coordinates in the triple-weight exchange. -/
theorem finite_subtraction_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x : G) (f : G → ℕ) :
    (∑ y ∈ S, f (x - y)) = ∑ a : G, if x - a ∈ S then f a else 0 := by
  rw [← Equiv.sum_comp (Equiv.subLeft x) (fun a ↦ if x - a ∈ S then f a else 0)]
  change (∑ y ∈ S, f (x - y)) = ∑ y : G, if x - (x - y) ∈ S then f (x - y) else 0
  simp only [sub_sub_cancel, Finset.sum_ite_mem, Finset.univ_inter]

/-- For a fixed common point x, a double difference sum equals the ambient
weight multiplied by its two reflected incidence indicators. Change each
coordinate separately. This retains arbitrary joint weights F(a,b). -/
theorem finite_double_subtraction_sum {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x : G) (F : G → G → ℕ) :
    (∑ y : S, ∑ z : S, F (x - y.val) (x - z.val)) =
      ∑ a : G, ∑ b : G, F a b * (if x - a ∈ S then 1 else 0) * (if x - b ∈ S then 1 else 0) := by
  rw [Finset.sum_coe_sort S (fun y ↦ ∑ z : S, F (x - y) (x - z.val))]
  have hz (y : G) : (∑ z : S, F (x - y) (x - z.val)) = ∑ z ∈ S, F (x - y) (x - z) :=
    Finset.sum_coe_sort S (fun z ↦ F (x - y) (x - z))
  simp only [hz]
  rw [finite_subtraction_sum S x (fun a ↦ ∑ z ∈ S, F a (x - z))]
  apply Finset.sum_congr rfl
  intro a _
  rw [finite_subtraction_sum S x (F a)]
  by_cases ha : x - a ∈ S
  · simp only [ha, ite_true, mul_one, mul_ite, mul_zero]
  · simp only [ha, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]

/-- An arbitrary joint difference weight summed over actual triples in S
equals its ambient sum against the exact three-point correlation. Apply
the fixed-point coordinate exchange and interchange finite sums. This
rewrites the amplified triple sum before applying Cauchy–Schwarz. -/
theorem finite_triple_weight_exchange {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (F : G → G → ℕ) :
    (∑ x : S, ∑ y : S, ∑ z : S, F (x.val - y.val) (x.val - z.val)) =
      ∑ a : G, ∑ b : G, F a b * finiteTripleCorrelation S a b := by
  simp_rw [finite_double_subtraction_sum S]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset G))]
  simp only [finiteTripleCorrelation, Finset.mul_sum, mul_assoc]

end PseudoPrime.Analysis
