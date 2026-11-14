/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FastBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FirstZeros

/-! # From endpoint certificates to critical-line zeros -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For rational `14 ≤ a` with `a + 1/100 ≤ 100`, successful phase checks and opposite
finite-value margins imply opposite xi signs at the two endpoints. This supplies the finite
sign-change hypothesis needed for the complete low-zero family. -/
theorem endpoint_checked_signs (a : ℚ) (ha : 14 ≤ a) (hb : a + 1 / 100 ≤ 100)
    (hL : endpointPrecisePhaseCheck a = true) (hU : endpointPrecisePhaseCheck (a + 1 / 100) = true)
    (h :
      ((endpointFastRotated a).1 < (-913 / 10000000 : ℚ) ∧
          (913 / 10000000 : ℚ) < (endpointFastRotated (a + 1 / 100)).1) ∨
        ((endpointFastRotated (a + 1 / 100)).1 < (-913 / 10000000 : ℚ) ∧
          (913 / 10000000 : ℚ) < (endpointFastRotated a).1)) :
    let f := fun t : ℝ ↦ (RiemannXi.riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re
    (f a < 0 ∧ 0 < f ((a + 1 / 100 : ℚ) : ℝ)) ∨ (f ((a + 1 / 100 : ℚ) : ℝ) < 0 ∧ 0 < f a) := by
  have ha100 : a ≤ 100 := by linarith only [hb]
  have hb14 : 14 ≤ a + 1 / 100 := by linarith only [ha]
  have haR : (14 : ℝ) ≤ a := by exact_mod_cast ha
  have hbR : (14 : ℝ) ≤ ((a + 1 / 100 : ℚ) : ℝ) := by exact_mod_cast hb14
  rcases h with h | h
  · have hl := endpoint_fast_negative_margin a ha ha100 hL h.1
    have hu := endpoint_fast_positive_margin (a + 1 / 100) hb14 hb hU h.2
    right
    exact
      ⟨(RiemannXi.normalized_zeta_xi_sign hbR).1 (by linarith only [hu]),
        (RiemannXi.normalized_zeta_xi_sign haR).2 (by linarith only [hl])⟩
  · have hu := endpoint_fast_negative_margin (a + 1 / 100) hb14 hb hU h.1
    have hl := endpoint_fast_positive_margin a ha ha100 hL h.2
    left
    exact
      ⟨(RiemannXi.normalized_zeta_xi_sign haR).1 (by linarith only [hl]),
        (RiemannXi.normalized_zeta_xi_sign hbR).2 (by linarith only [hu])⟩

/-- For rational `14 ≤ a` with `a + 1/100 ≤ 100`, successful phase checks and opposite
finite-value margins imply a critical-line zeta zero in the open interval. This combines the
uniform approximation error with the normalized-sign and intermediate-value theorems. -/
theorem exists_zero_of_endpoint_checks (a : ℚ) (ha : 14 ≤ a) (hb : a + 1 / 100 ≤ 100)
    (hL : endpointPrecisePhaseCheck a = true) (hU : endpointPrecisePhaseCheck (a + 1 / 100) = true)
    (h :
      ((endpointFastRotated a).1 < (-913 / 10000000 : ℚ) ∧
          (913 / 10000000 : ℚ) < (endpointFastRotated (a + 1 / 100)).1) ∨
        ((endpointFastRotated (a + 1 / 100)).1 < (-913 / 10000000 : ℚ) ∧
          (913 / 10000000 : ℚ) < (endpointFastRotated a).1)) :
    ∃ t ∈ Set.Ioo (a : ℝ) ((a + 1 / 100 : ℚ) : ℝ),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have ha100 : a ≤ 100 := by linarith only [hb]
  have hb14 : 14 ≤ a + 1 / 100 := by linarith only [ha]
  have haR : (14 : ℝ) ≤ a := by exact_mod_cast ha
  have hab : (a : ℝ) < ((a + 1 / 100 : ℚ) : ℝ) := by
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    linarith only
  apply exists_zero_of_normalized_signs haR hab
  rcases h with h | h
  · left
    have hl := endpoint_fast_negative_margin a ha ha100 hL h.1
    have hu := endpoint_fast_positive_margin (a + 1 / 100) hb14 hb hU h.2
    constructor <;> linarith only [hl, hu]
  · right
    have hu := endpoint_fast_negative_margin (a + 1 / 100) hb14 hb hU h.1
    have hl := endpoint_fast_positive_margin a ha ha100 hL h.2
    constructor <;> linarith only [hl, hu]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
