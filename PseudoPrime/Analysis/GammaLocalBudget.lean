/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-! # Common dual budget for Gamma local corrections

Euler and ramp losses share one weight budget; their positive excess is kept together.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a finite set, nonnegative weights, and a nonnegative dual parameter.
Claim: local costs are bounded by a common weight budget and their positive excess.
Proof: bound each cost by the dual parameter plus its positive excess and sum.
Role: combine ramified Euler and arithmetic losses under one conductor budget. -/
theorem ramified_cost_le_dual_cap {ι : Type*} (S : Finset ι) (w A : ι → ℝ) {μ L : ℝ} (hμ : 0 ≤ μ)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hbudget : ∑ i ∈ S, w i ≤ L) :
    ∑ i ∈ S, w i * A i ≤ μ * L + ∑ i ∈ S, w i * max (A i - μ) 0 := by
  have hpoint : ∀ i ∈ S, w i * A i ≤ w i * (μ + max (A i - μ) 0) := fun i hi ↦
    mul_le_mul_of_nonneg_left (by linarith only [le_max_left (A i - μ) 0]) (hw i hi)
  calc
    _ ≤ ∑ i ∈ S, w i * (μ + max (A i - μ) 0) := Finset.sum_le_sum hpoint
    _ = μ * (∑ i ∈ S, w i) + ∑ i ∈ S, w i * max (A i - μ) 0 := by
      rw [Finset.sum_congr rfl (fun i _ ↦ mul_add (w i) μ _), Finset.sum_add_distrib, ←
        Finset.sum_mul, mul_comm (∑ i ∈ S, w i) μ]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hbudget hμ) le_rfl

/-- Input: finite ramified data with a common nonnegative weight budget.
Claim: the sum of Euler and ramp losses uses the budget only once.
Proof: specialize the dual-cap theorem to the sum of the two local costs.
Role: expose the joint local correction required by the signed witness comparison. -/
theorem ramified_joint_cost_le_dual_cap {ι : Type*} (S : Finset ι) (w Euler Ramp : ι → ℝ) {μ L : ℝ}
    (hμ : 0 ≤ μ) (hw : ∀ i ∈ S, 0 ≤ w i) (hbudget : ∑ i ∈ S, w i ≤ L) :
    ∑ i ∈ S, w i * (Euler i + Ramp i) ≤ μ * L + ∑ i ∈ S, w i * max (Euler i + Ramp i - μ) 0 :=
  ramified_cost_le_dual_cap S w (fun i ↦ Euler i + Ramp i) hμ hw hbudget

end PseudoPrime.Analysis
