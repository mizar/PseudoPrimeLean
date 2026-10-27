/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaFiniteEulerRowBlocks

/-! # Composition and extension of finite Euler interval lower bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Lower bounds on adjacent natural intervals add to a lower bound
on their union. The endpoints are ordered. Split the finite sum across
the disjoint intervals and add the real casts of the rational allowances. -/
theorem gamma_euler_interval_lower_add {lo mid hi : ℕ} {c d : ℚ} (hl : lo ≤ mid) (hh : mid ≤ hi)
    (hc : (c : ℝ) ≤ ∑ m ∈ Finset.Ioc lo mid, gammaResolventMangoldtWeight m)
    (hd : (d : ℝ) ≤ ∑ m ∈ Finset.Ioc mid hi, gammaResolventMangoldtWeight m) :
    ((c + d : ℚ) : ℝ) ≤ ∑ m ∈ Finset.Ioc lo hi, gammaResolventMangoldtWeight m := by
  have hdis : Disjoint (Finset.Ioc lo mid) (Finset.Ioc mid hi) := by
    apply Finset.disjoint_left.mpr
    intro m hm hn
    exact (not_lt_of_ge (Finset.mem_Ioc.mp hm).2) (Finset.mem_Ioc.mp hn).1
  rw [← Finset.Ioc_union_Ioc_eq_Ioc hl hh, Finset.sum_union hdis, Rat.cast_add]
  exact add_le_add hc hd

/-- A certified Euler prefix lower bound remains valid at a larger
cutoff. All actual Mangoldt Euler weights are nonnegative, so adding
inputs preserves the lower bound. This extends the final block endpoint. -/
theorem gamma_euler_prefix_lower_mono {b B : ℕ} {c : ℚ} (hb : b ≤ B)
    (hc : (c : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 b, gammaResolventMangoldtWeight m) :
    (c : ℝ) ≤ ∑ m ∈ Finset.Ioc 0 B, gammaResolventMangoldtWeight m := by
  apply hc.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1, (Finset.mem_Ioc.mp hm).2.trans hb⟩
  · intro m _ _
    exact gammaResolventMangoldtWeight_nonneg m

end PseudoPrime.Analysis
