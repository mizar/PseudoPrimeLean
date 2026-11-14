/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100FirstMargins
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalLineZeros

/-! # Zeros in the first three low-zero intervals -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `14 ≤ a < b`, opposite signs of normalized zeta at the endpoints imply a critical-line
zeta zero in `(a,b)`. The phase sign relation gives opposite xi signs, and continuity supplies
the zero. The result is independent of RH and can be reused for every certified interval. -/
theorem exists_zero_of_normalized_signs {a b : ℝ} (ha : 14 ≤ a) (hab : a < b)
    (hs :
      (RiemannXi.normalizedZeta a < 0 ∧ 0 < RiemannXi.normalizedZeta b) ∨
        (RiemannXi.normalizedZeta b < 0 ∧ 0 < RiemannXi.normalizedZeta a)) :
    ∃ t ∈ Set.Ioo a b, riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  have hb : 14 ≤ b := le_trans ha hab.le
  apply RiemannXi.exists_critical_zeta_zero_of_sign hab
  rcases hs with h | h
  · exact
      Or.inr
        ⟨(RiemannXi.normalized_zeta_xi_sign hb).1 h.2, (RiemannXi.normalized_zeta_xi_sign ha).2 h.1⟩
  · exact
      Or.inl
        ⟨(RiemannXi.normalized_zeta_xi_sign ha).1 h.2, (RiemannXi.normalized_zeta_xi_sign hb).2 h.1⟩

/-- The first candidate interval contains a zero of zeta on the critical line. The endpoint
margins prove a sign change, and continuity supplies the zero without assuming RH. -/
theorem low_zero_first_exists :
    ∃ t ∈ Set.Ioo (14473 / 1024 : ℝ) (14473 / 1024 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  apply exists_zero_of_normalized_signs (by norm_num only) (by norm_num only)
  left
  have h := low_zero_first_three_margins
  constructor <;> norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  · linarith only [h.1]
  · linarith only [h.2.1]

/-- The second candidate interval contains a zero of zeta on the critical line. The endpoint
margins prove a sign change, and continuity supplies the zero without assuming RH. -/
theorem low_zero_second_exists :
    ∃ t ∈ Set.Ioo (10763 / 512 : ℝ) (10763 / 512 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  apply exists_zero_of_normalized_signs (by norm_num only) (by norm_num only)
  right
  have h := low_zero_first_three_margins
  constructor <;> norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  · linarith only [h.2.2.2.1]
  · linarith only [h.2.2.1]

/-- The third candidate interval contains a zero of zeta on the critical line. The endpoint
margins prove a sign change, and continuity supplies the zero without assuming RH. -/
theorem low_zero_third_exists :
    ∃ t ∈ Set.Ioo (25611 / 1024 : ℝ) (25611 / 1024 + 1 / 100),
      riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = 0 := by
  apply exists_zero_of_normalized_signs (by norm_num only) (by norm_num only)
  left
  have h := low_zero_first_three_margins
  constructor <;> norm_num only [Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat] at h ⊢
  · linarith only [h.2.2.2.2.1]
  · linarith only [h.2.2.2.2.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
