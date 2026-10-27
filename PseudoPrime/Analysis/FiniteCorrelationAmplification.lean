/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RegularKernelAmplification
public import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Tactic.Abel

/-! # Amplification of actual finite difference correlations -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Count ordered pairs in S with difference d by their second coordinate.
The indicator sum is natural-valued and is used for both energy and overlaps.
It applies to arbitrary finite subsets of a finite additive commutative group. -/
def finiteDifferenceCorrelation {G : Type*} [AddCommGroup G] [DecidableEq G] (S : Finset G)
    (d : G) : ℕ :=
  ∑ y ∈ S, if d + y ∈ S then 1 else 0

/-- The incidence column at difference d has mass equal to the difference
correlation. Replace a sum over the subtype S by its finite-set sum. This
provides the exact column energy in the matrix amplification inequality. -/
theorem finiteDifferenceCorrelation_eq_subtype {G : Type*} [AddCommGroup G] [DecidableEq G]
    (S : Finset G) (d : G) :
    finiteDifferenceCorrelation S d = ∑ y : S, if d + y.val ∈ S then 1 else 0 := by
  exact Finset.sum_subtype S (fun _ ↦ Iff.rfl) _

/-- The overlap of the translated incidence columns indexed by y and z is
the correlation at y-z. Translate the ambient summation variable by z and
restrict to S. This identifies matrix entry energy with a triple correlation. -/
theorem finite_incidence_overlap {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (y z : G) :
    (∑ a : G, (if a + y ∈ S then 1 else 0 : ℕ) * (if a + z ∈ S then 1 else 0)) =
      finiteDifferenceCorrelation S (y - z) := by
  rw [←
    (Equiv.subRight z).sum_comp
      (fun a ↦ (if a + y ∈ S then 1 else 0 : ℕ) * (if a + z ∈ S then 1 else 0))]
  change (∑ b : G, (if b - z + y ∈ S then 1 else 0 : ℕ) * (if b - z + z ∈ S then 1 else 0)) = _
  have he (b : G) : b - z + y = (y - z) + b := by abel
  simp only [he, sub_add_cancel]
  have hi (b : G) :
    (if (y - z) + b ∈ S then 1 else 0 : ℕ) * (if b ∈ S then 1 else 0) =
      if b ∈ S then (if (y - z) + b ∈ S then 1 else 0) else 0 := by
    split_ifs <;> rfl
  simp only [hi, Finset.sum_ite_mem, Finset.univ_inter, finiteDifferenceCorrelation]

/-- An even difference weight with constant row mass on S gives B²E≤t³Q.
Here B is its actual pair sum, E the full difference energy, and Q the
weighted triple correlation. Apply regular-kernel amplification and the
proved incidence identities, so no column-sum or overlap hypothesis remains. -/
theorem finite_correlation_energy_amplification {G : Type*} [AddCommGroup G] [Fintype G]
    [DecidableEq G] (S : Finset G) (g : G → ℕ) (μ : ℕ) (he : ∀ a, g (-a) = g a)
    (hr : ∀ x : S, ∑ y : S, g (x.val - y.val) = μ) :
    (∑ x : S, ∑ y : S, g (x.val - y.val)) ^ 2 * (∑ a : G, finiteDifferenceCorrelation S a ^ 2) ≤
      S.card ^ 3 *
        ∑ x : S,
          ∑ y : S,
            ∑ z : S,
              g (x.val - y.val) * g (x.val - z.val) *
                finiteDifferenceCorrelation S (y.val - z.val) := by
  have hs (x y : S) : g (x.val - y.val) = g (y.val - x.val) := by rw [← neg_sub x.val y.val, he]
  have h :=
    regular_kernel_energy_amplification (fun x y : S ↦ g (x.val - y.val))
      (fun (y : S) a ↦ if a + y.val ∈ S then 1 else 0) μ hs hr
  simpa only [← finiteDifferenceCorrelation_eq_subtype, finite_incidence_overlap,
    Fintype.card_coe] using h

/-- A weighted pair sum equals the weight times the exact difference count,
summed over all ambient differences. Translate by the second coordinate
and interchange finite sums. This identifies selected pair mass with the
energy retained by a correlation level. -/
theorem finite_pair_sum_eq_correlation {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (S : Finset G) (g : G → ℕ) :
    (∑ x ∈ S, ∑ y ∈ S, g (x - y)) = ∑ a : G, g a * finiteDifferenceCorrelation S a := by
  simp only [finiteDifferenceCorrelation, Finset.mul_sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_comm (s := S) (t := S), Finset.sum_comm (s := Finset.univ) (t := S)]
  apply Finset.sum_congr rfl
  intro y _
  rw [← (Equiv.subRight y).sum_comp (fun a ↦ if a + y ∈ S then g a else 0)]
  change (∑ x ∈ S, g (x - y)) = ∑ x : G, if (x - y) + y ∈ S then g (x - y) else 0
  simp only [sub_add_cancel, Finset.sum_ite_mem, Finset.univ_inter]

end PseudoPrime.Analysis
