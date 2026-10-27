/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.BigOperators.Ring.List

/-! # Finite list combinations of convergent real infinite sums -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite list of summable real-valued functions has a summable pointwise sum.
Induct over the list and add the convergence statements. Repeated indices are retained.
This justifies summing signed finite combinations of zero kernels. -/
theorem summable_list_sum {ι κ : Type*} (l : List ι) (f : ι → κ → ℝ) (h : ∀ i ∈ l, Summable (f i)) :
    Summable (fun x ↦ (l.map (fun i ↦ f i x)).sum) := by
  induction l with
  | nil =>
    simpa only [List.map_nil, List.sum_nil] using (summable_zero : Summable (fun _ : κ ↦ (0 : ℝ)))
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have hl := ih (fun j hj ↦ h j (List.mem_cons_of_mem i hj))
    simpa only [List.map_cons, List.sum_cons] using hi.add hl

/-- For a finite list of summable real-valued functions, the infinite sum commutes with
the finite list sum. Induct over the list and use additivity of convergent infinite sums.
No positivity or distinctness assumption is required, allowing signed resolvent coefficients. -/
theorem tsum_list_sum {ι κ : Type*} (l : List ι) (f : ι → κ → ℝ) (h : ∀ i ∈ l, Summable (f i)) :
    (∑' x, (l.map (fun i ↦ f i x)).sum) = (l.map (fun i ↦ ∑' x, f i x)).sum := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, tsum_zero]
  | cons i l ih =>
    have hi := h i List.mem_cons_self
    have hl := fun j hj ↦ h j (List.mem_cons_of_mem i hj)
    simp only [List.map_cons, List.sum_cons]
    rw [hi.tsum_add (summable_list_sum l f hl), ih hl]

end PseudoPrime.Analysis
