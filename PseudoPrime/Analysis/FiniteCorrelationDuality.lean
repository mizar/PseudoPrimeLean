/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteCorrelationAmplification

/-! # Finite Gram duality and reflected difference incidence -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The squared overlap mass of the columns of a natural-valued matrix
equals that of its rows. Expand both squares and interchange the four
finite sums. This supplies the exact third-energy identity for incidence
matrices without any analytic hypothesis or cardinality bound. -/
theorem finite_gram_square_duality {ι α : Type*} [Fintype ι] [Fintype α] (v : ι → α → ℕ) :
    (∑ a, ∑ b, (∑ x, v x a * v x b) ^ 2) = ∑ x, ∑ y, (∑ a, v x a * v y a) ^ 2 := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset ι))]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The overlap of two reflected translates of a finite set is its exact
difference correlation. Negate the ambient summation variable and apply
the translated-incidence identity. This computes row overlaps in Gram duality. -/
theorem finite_reflected_incidence_overlap {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (x y : G) :
    (∑ a : G, (if x - a ∈ S then 1 else 0 : ℕ) * (if y - a ∈ S then 1 else 0)) =
      finiteDifferenceCorrelation S (x - y) := by
  rw [←
    Equiv.sum_comp (Equiv.neg G)
      (fun a ↦ (if x - a ∈ S then 1 else 0 : ℕ) * (if y - a ∈ S then 1 else 0))]
  change (∑ a : G, (if x - (-a) ∈ S then 1 else 0 : ℕ) * (if y - (-a) ∈ S then 1 else 0)) = _
  simp only [sub_neg_eq_add, add_comm x, add_comm y]
  exact finite_incidence_overlap S x y

/-- The weighted pair sum over the subtype of S equals the weight times
its difference correlation. Convert the two subtype sums and apply the
proved finite-set identity. This interface avoids repeated subtype conversions. -/
theorem finite_subtype_pair_sum_eq_correlation {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (S : Finset G) (g : G → ℕ) :
    (∑ x : S, ∑ y : S, g (x.val - y.val)) = ∑ a : G, g a * finiteDifferenceCorrelation S a := by
  rw [Finset.sum_coe_sort S (fun x ↦ ∑ y : S, g (x - y.val))]
  calc
    _ = ∑ x ∈ S, ∑ y ∈ S, g (x - y) :=
      Finset.sum_congr rfl (fun x _ ↦ Finset.sum_coe_sort S (fun y ↦ g (x - y)))
    _ = _ := finite_pair_sum_eq_correlation S g

end PseudoPrime.Analysis
