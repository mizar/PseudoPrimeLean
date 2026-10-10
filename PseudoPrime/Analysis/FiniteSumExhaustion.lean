/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Finite exhaustions of absolutely summable families

Finite sets need only eventually contain each nonzero term; they need not be nested.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For an absolutely summable family in a complete normed additive group, finite sums
converge to its tsum if every nonzero term eventually belongs to the chosen finite sets.
Extend each finite sum by zero and apply dominated convergence with the term norms.
This permits contour zero ledgers to grow along nonmonotone good-height sequences. -/
theorem tendsto_sum_of_eventually_mem_support {α : Type*} {G : Type*} [NormedAddCommGroup G]
    [CompleteSpace G] (f : α → G) (hf : Summable (fun a => ‖f a‖)) (S : ℕ → Finset α)
    (hS : ∀ a, f a ≠ 0 → ∀ᶠ n in Filter.atTop, a ∈ S n) :
    Filter.Tendsto (fun n => ∑ a ∈ S n, f a) Filter.atTop (nhds (∑' a, f a)) := by
  classical
  let F := fun n a => if a ∈ S n then f a else 0
  have heq (n : ℕ) : ∑' a, F n a = ∑ a ∈ S n, f a := by
    rw [tsum_eq_sum (fun a ha => ite_eq_right ha)]
    exact Finset.sum_congr rfl (fun a ha => ite_eq_left ha)
  have hlim (a : α) : Filter.Tendsto (fun n => F n a) Filter.atTop (nhds (f a)) := by
    by_cases ha : f a = 0
    · have he : (fun n => F n a) = fun _ => (0 : G) := by
        funext n
        simp only [F, ha, ite_self]
      rw [he, ha]
      exact tendsto_const_nhds
    · apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [hS a ha] with n hn
      exact (ite_eq_left hn).symm
  have hb : ∀ᶠ n in Filter.atTop, ∀ a, ‖F n a‖ ≤ ‖f a‖ :=
    Filter.Eventually.of_forall fun n a => by
      by_cases ha : a ∈ S n
      · rw [show F n a = f a from ite_eq_left ha]
      · rw [show F n a = 0 from ite_eq_right ha, norm_zero]
        exact norm_nonneg _
  exact (tendsto_tsum_of_dominated_convergence hf hlim hb).congr heq

end PseudoPrime.Analysis
