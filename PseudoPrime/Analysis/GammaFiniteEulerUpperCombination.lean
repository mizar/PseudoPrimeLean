/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerSupport

/-! # Composition of certified finite Euler interval upper bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Certified upper allowances for adjacent ordered intervals add to
an upper allowance for their whole union. Split the actual finite sum
at the shared endpoint and commute the rational addition cast. This
is the balanced-tree interface for the finite prefix upper certificate. -/
theorem gamma_euler_interval_upper_add {lo mid hi : ℕ} {c d : ℚ} (hl : lo ≤ mid) (hh : mid ≤ hi)
    (hc : (∑ m ∈ Finset.Ioc lo mid, gammaResolventMangoldtWeight m) ≤ (c : ℝ))
    (hd : (∑ m ∈ Finset.Ioc mid hi, gammaResolventMangoldtWeight m) ≤ (d : ℝ)) :
    (∑ m ∈ Finset.Ioc lo hi, gammaResolventMangoldtWeight m) ≤ ((c + d : ℚ) : ℝ) := by
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro m hm hn
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp hn).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add hc hd

end PseudoPrime.Analysis
