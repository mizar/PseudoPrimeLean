/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.CellSound

/-! # Real estimates extracted from the joint Boolean cell check -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- Numerator and denominator of the theta coefficient for a cell starting at `a`. -/
def thetaBand (a : ℕ) : ℕ × ℕ :=
  if a < 3100 then (9, 5) else if a < 3500 then (19, 10) else (97, 50)

private theorem band_gap (a : ℕ) :
    let u := (thetaBand a).1
    let v := (thetaBand a).2
    0 < v ∧ ((5 * u - 4 * v : ℕ) : ℝ) / (5 * v : ℕ) = (u : ℝ) / v - 4 / 5 := by
  by_cases hl : a < 3100
  · norm_num only [and_self, thetaBand, ite_eq_left hl]
  · by_cases hm : a < 3500
    · norm_num only [and_self, thetaBand, ite_eq_right hl, ite_eq_left hm]
    · norm_num only [and_self, thetaBand, ite_eq_right hl, ite_eq_right hm]

/-- The Boolean cell check certifies psi throughout the cell, and theta from 2657
when the chosen psi coefficient is at most four fifths. Both bounds use scalar prefixes. -/
theorem cellCheck_sound {a b l h d e L H D E u v : ℕ} {x : ℝ} (sa : Prefix a l h d e)
    (sb : Prefix (b - 1) L H D E) (hv : 0 < v) (hc : (u : ℝ) / v ≤ 2) (ha : (1 : ℝ) ≤ a)
    (hx : (a : ℝ) ≤ x) (hb : x < b) (hg : cellCheck a b u v l (l - d) H E = true) :
    |Chebyshev.psi x - x| ≤ ((u : ℝ) / v) * Real.sqrt x ∧
      (2657 ≤ a →
        (u : ℝ) / v ≤ 4 / 5 →
        |Chebyshev.theta x - x| ≤ ((thetaBand a).1 / ((thetaBand a).2 : ℝ)) * Real.sqrt x) := by
  obtain ⟨⟨hh, hl⟩, ht⟩ :=
    (show
      (within (H - scale * a) a u v = true ∧ within (scale * b - l) b u v = true) ∧
        ((a < 2657 ||
              within E a (5 * (thetaBand a).1 - 4 * (thetaBand a).2) (5 * (thetaBand a).2)) ||
            within (scale * b - (l - d)) b (thetaBand a).1 (thetaBand a).2) =
          true
      by simpa only [cellCheck, thetaBand, Bool.and_eq_true] using hg)
  have hp := psi_cell_of_prefix sa sb hv hc ha hx hb hl hh
  refine ⟨hp, fun hcut hc' ↦ ?_⟩
  have hg' := band_gap a
  apply
    theta_cell_of_guards (u := (thetaBand a).1) (v := (thetaBand a).2) sa sb hx hb hg'.1
      (hg'.2.le.trans (sub_le_sub_left hc' _)) hp
  simpa only [decide_eq_false (Nat.not_lt_of_ge hcut), Bool.false_or] using ht

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
