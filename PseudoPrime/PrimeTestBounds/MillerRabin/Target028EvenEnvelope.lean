/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalFullEnvelope

/-! # Even-correction interval bound for coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An even-character anchor bounds the local envelope by the 0.28 cutoff
throughout a logarithmic interval when the weighted budget and logarithmic
count fit the shifted radius. The rational factor `52915/100000` squares
below `7/25`, so the two endpoint comparisons suffice for the full cell. -/
theorem target028_semiprime_anchor_envelope {n : ℕ} {A D lo hi : ℝ} {b d : ℚ} {j : ℕ}
    (hm : (b, d, j) ∈ localEvenAnchors) (hb0 : (0 : ℝ) ≤ b) (hlo : lo ≤ Real.log n)
    (hhi : Real.log n ≤ hi) (hb : (b : ℝ) ≤ (52915 / 100000 : ℝ) * lo)
    (hleft : A ≤ (52915 / 100000 : ℝ) * lo + d) (hright : (1 - 52915 / 100000 : ℝ) * hi ≤ D + d) :
    localFullEnvelope (max A (Real.log n - D)) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by
  have heven :
    localEvenEnvelope (max A (Real.log n - D)) ≤ (max (b : ℝ) (max A (Real.log n - D) - d)) ^ 2 :=
    Finset.inf'_le _ (List.mem_toFinset.mpr hm)
  have hbound : max (b : ℝ) (max A (Real.log n - D) - d) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hb, hlo]
    · apply sub_le_iff_le_add.mpr
      apply max_le
      · linarith only [hleft, hlo]
      · linarith only [hright, hhi]
  have hnonneg : 0 ≤ max (b : ℝ) (max A (Real.log n - D) - d) := hb0.trans (le_max_left _ _)
  have hs := mul_self_le_mul_self hnonneg hbound
  have hLsq := sq_nonneg (Real.log n)
  exact (min_le_right _ _).trans (heven.trans (by nlinarith only [hs, hLsq]))

end PseudoPrime.PrimeTestBounds.MillerRabin
