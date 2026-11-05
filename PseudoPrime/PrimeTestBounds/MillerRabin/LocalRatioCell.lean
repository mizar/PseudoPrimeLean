/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeFactorLocalEnvelope

/-! # Even-anchor ratio cells for the three-factor branch -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational scale interval and one even anchor used to bound the local radius on it.
The anchor correction and its binary scale must occur in the certified anchor table. -/
structure LocalRatioCell where
  /-- Anchor radius. -/
  b : ℚ
  /-- Certified correction. -/
  d : ℚ
  /-- Binary scale for the anchor certificate. -/
  j : ℕ
  /-- Left endpoint. -/
  lo : ℚ
  /-- Right endpoint. -/
  hi : ℚ

/-- Check anchor membership and the endpoint inequalities ensuring its radius is at most
`(96467/100000) * s` throughout the nonnegative interval. -/
def LocalRatioCell.check (c : LocalRatioCell) : Bool :=
  decide
    ((c.b, c.d, c.j) ∈ localEvenAnchors ∧
      0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.b ≤ (96467 / 100000) * c.lo ∧ (1 - 96467 / 100000) * c.hi ≤ c.d)

/-- A checked cell bounds the common local envelope by the squared `96467/100000`
multiple of the scale throughout its interval. The endpoint inequalities bound both
parts of the anchor maximum, and its certified radius is one candidate in the envelope. -/
theorem LocalRatioCell.sound (c : LocalRatioCell) (hcheck : c.check = true) {s : ℝ}
    (hlo : (c.lo : ℝ) ≤ s) (hhi : s ≤ (c.hi : ℝ)) :
    localFullEnvelope s ≤ ((96467 / 100000 : ℝ) * s) ^ 2 := by
  have hc :
    (c.b, c.d, c.j) ∈ localEvenAnchors ∧
      0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.b ≤ (96467 / 100000) * c.lo ∧ (1 - 96467 / 100000) * c.hi ≤ c.d :=
    of_decide_eq_true hcheck
  have hbq : (8 : ℚ) ≤ c.b :=
    (of_decide_eq_true ((List.all_eq_true.mp localEvenAnchors_checked) _ hc.1)).1
  have hb : (8 : ℝ) ≤ c.b := by exact_mod_cast hbq
  have hsmall := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.1
  have hlarge := (Rat.cast_le (K := ℝ)).mpr hc.2.2.2.2
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hsmall hlarge
  have hlo0 : (0 : ℝ) ≤ c.lo := by exact_mod_cast hc.2.1
  have hs0 : 0 ≤ s := hlo0.trans hlo
  have hbhi : (c.b : ℝ) ≤ (96467 / 100000 : ℝ) * s := by nlinarith only [hsmall, hlo]
  have hsub : s - (c.d : ℝ) ≤ (96467 / 100000 : ℝ) * s := by nlinarith only [hlarge, hhi]
  have hmax : max (c.b : ℝ) (s - c.d) ≤ (96467 / 100000 : ℝ) * s := max_le hbhi hsub
  have hmax0 : 0 ≤ max (c.b : ℝ) (s - c.d) := by
    have h := le_max_left (c.b : ℝ) (s - c.d)
    linarith only [hb, h]
  have hsq := pow_le_pow_left₀ hmax0 hmax 2
  have heven : localEvenEnvelope s ≤ (max (c.b : ℝ) (s - c.d)) ^ 2 :=
    Finset.inf'_le _ (List.mem_toFinset.mpr hc.1)
  exact (min_le_right _ _).trans (heven.trans hsq)

end PseudoPrime.PrimeTestBounds.MillerRabin
