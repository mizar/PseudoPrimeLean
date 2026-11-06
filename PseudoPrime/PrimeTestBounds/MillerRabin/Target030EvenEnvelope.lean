/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Local

/-! # Even-correction interval bound for 0.30 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first certified even-character correction bounds the local envelope
on an interval when both weighted budgets fit its shifted 0.30 radius. -/
theorem target030_semiprime_even_envelope {n : ℕ} {A D lo hi : ℝ} (hlo : lo ≤ Real.log n)
    (hhi : Real.log n ≤ hi) (hb : (8 : ℝ) ≤ (5477 / 10000 : ℝ) * lo)
    (hleft : A ≤ (5477 / 10000 : ℝ) * lo + 324969 / 100000)
    (hright : hi - D ≤ (5477 / 10000 : ℝ) * lo + 324969 / 100000) :
    localFullEnvelope (max A (Real.log n - D)) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
  have hm : ((8 : ℚ), (324969 / 100000 : ℚ), 3) ∈ localEvenAnchors := by exact List.mem_cons_self
  have heven :
    localEvenEnvelope (max A (Real.log n - D)) ≤
      (max (8 : ℝ) (max A (Real.log n - D) - 324969 / 100000)) ^ 2 := by
    have h :
      localEvenEnvelope (max A (Real.log n - D)) ≤
        (max ((8 : ℚ) : ℝ) (max A (Real.log n - D) - ((324969 / 100000 : ℚ) : ℝ))) ^ 2 :=
      Finset.inf'_le _ (List.mem_toFinset.mpr hm)
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  have hbound :
    max (8 : ℝ) (max A (Real.log n - D) - 324969 / 100000) ≤ (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hb, hlo]
    · apply sub_le_iff_le_add.mpr
      apply max_le
      · linarith only [hleft, hlo]
      · linarith only [hright, hhi, hlo]
  have hnonneg : 0 ≤ max (8 : ℝ) (max A (Real.log n - D) - 324969 / 100000) :=
    (by norm_num only : (0 : ℝ) ≤ 8).trans (le_max_left _ _)
  have hs := mul_self_le_mul_self hnonneg hbound
  have hLsq := sq_nonneg (Real.log n)
  exact (min_le_right _ _).trans (heven.trans (by nlinarith only [hs, hLsq]))

/-- Any certified even anchor bounds the local envelope on an interval when
the budget and logarithmic count fit its shifted 0.30 radius. -/
theorem target030_semiprime_anchor_envelope {n : ℕ} {A D lo hi : ℝ} {b d : ℚ} {j : ℕ}
    (hm : (b, d, j) ∈ localEvenAnchors) (hb0 : (0 : ℝ) ≤ b) (hlo : lo ≤ Real.log n)
    (hhi : Real.log n ≤ hi) (hb : (b : ℝ) ≤ (5477 / 10000 : ℝ) * lo)
    (hleft : A ≤ (5477 / 10000 : ℝ) * lo + d) (hright : hi - D ≤ (5477 / 10000 : ℝ) * lo + d) :
    localFullEnvelope (max A (Real.log n - D)) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
  have heven :
    localEvenEnvelope (max A (Real.log n - D)) ≤ (max (b : ℝ) (max A (Real.log n - D) - d)) ^ 2 :=
    Finset.inf'_le _ (List.mem_toFinset.mpr hm)
  have hbound : max (b : ℝ) (max A (Real.log n - D) - d) ≤ (5477 / 10000 : ℝ) * Real.log n := by
    apply max_le
    · linarith only [hb, hlo]
    · apply sub_le_iff_le_add.mpr
      apply max_le
      · linarith only [hleft, hlo]
      · linarith only [hright, hhi, hlo]
  have hnonneg : 0 ≤ max (b : ℝ) (max A (Real.log n - D) - d) := hb0.trans (le_max_left _ _)
  have hs := mul_self_le_mul_self hnonneg hbound
  have hLsq := sq_nonneg (Real.log n)
  exact (min_le_right _ _).trans (heven.trans (by nlinarith only [hs, hLsq]))

end PseudoPrime.PrimeTestBounds.MillerRabin
