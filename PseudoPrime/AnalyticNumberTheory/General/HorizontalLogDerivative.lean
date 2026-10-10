/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.GoodHeight

/-!
# Horizontal logarithmic derivative bounds at good heights

Positive distance from zero ordinates bounds the nearby poles, while the
completed-function nearby-zero approximation controls the remaining error.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A positive separation from every zero ordinate guarantees nonvanishing
at every point of height T. A zero at that height would have distance zero.
This makes the logarithmic derivative valid on the selected horizontal edge. -/
theorem nonzero_at_avoiding_height {F : ℂ → ℂ} {T c : ℝ} (hc : 0 < c)
    (ha : ∀ ρ : ℂ, F ρ = 0 → c ≤ |T - ρ.im|) {s : ℂ} (hs : s.im = T) : F s ≠ 0 := by
  intro hz
  have hh := ha s hz
  rw [hs, sub_self, abs_zero] at hh
  exact (not_le_of_gt hc) hh

/-- If every zero ordinate is separated from T by c>0, the nearby simple
resolvent at any point of height T is bounded by local multiplicity divided
by c. The imaginary part bounds the denominator; nonzero values have zero
multiplicity. This converts height separation into a pole-sum majorant. -/
theorem norm_nearZeroResolvent_le_of_avoiding_height {F : ℂ → ℂ} {T c : ℝ} (hc : 0 < c)
    (ha : ∀ ρ : ℂ, F ρ = 0 → c ≤ |T - ρ.im|) {s : ℂ} (hs : s.im = T) (ρ : ℂ) :
    ‖nearZeroResolventTerm F T s ρ‖ ≤ localZeroMultiplicity F T ρ / c := by
  classical
  by_cases hn : |T - ρ.im| < 1
  · simp only [nearZeroResolventTerm, ite_eq_left hn, norm_div, Complex.norm_natCast,
      localZeroMultiplicity, ite_eq_left hn.le]
    by_cases hz : F ρ = 0
    · have hdist : c ≤ ‖s - ρ‖ := by
        have hh := Complex.abs_im_le_norm (s - ρ)
        rw [Complex.sub_im, hs] at hh
        exact (ha ρ hz).trans hh
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hc hdist
    · have ho : analyticOrderNatAt F ρ = 0 := by
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz), ENat.toNat_zero]
      simp only [ho, Nat.cast_zero, zero_div, le_refl]
  · simp only [nearZeroResolventTerm, ite_eq_right hn, norm_zero]
    exact div_nonneg (localZeroMultiplicity_nonneg F T ρ) hc.le

/-- Positive height separation and a convergent local count imply absolute
convergence of the nearby resolvent sum and a norm bound by the count divided
by the margin. Pointwise domination justifies the norm and sum interchange.
This controls the nearby poles on a zero-avoiding horizontal contour edge. -/
theorem summable_nearZeroResolvent_and_bound_of_avoiding_height {F : ℂ → ℂ} {T c : ℝ} (hc : 0 < c)
    (ha : ∀ ρ : ℂ, F ρ = 0 → c ≤ |T - ρ.im|) {s : ℂ} (hs : s.im = T)
    (hm : Summable (localZeroMultiplicity F T)) :
    Summable (nearZeroResolventTerm F T s) ∧
      ‖∑' ρ : ℂ, nearZeroResolventTerm F T s ρ‖ ≤ (∑' ρ : ℂ, localZeroMultiplicity F T ρ) / c := by
  have hmajor := hm.div_const c
  have hb := norm_nearZeroResolvent_le_of_avoiding_height hc ha hs
  have hn := hmajor.of_nonneg_of_le (fun ρ ↦ norm_nonneg _) hb
  refine ⟨hn.of_norm, (norm_tsum_le_tsum_norm hn).trans ?_⟩
  have hh := hn.tsum_le_tsum hb hmajor
  rw [tsum_div_const] at hh
  exact hh

/-- For entire order-one completion data, the logarithmic derivative on a
zero-avoiding height is bounded by the local count divided by the separation
margin plus the nearby-zero approximation error. Nonvanishing follows from
separation. Combine the simple-pole majorant and the completed-function error
estimate to control a horizontal contour edge. -/
theorem norm_logDeriv_le_of_avoiding_height {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {T c : ℝ} (hc : 0 < c)
    (ha : ∀ ρ : ℂ, F ρ = 0 → c ≤ |T - ρ.im|) {s : ℂ} (hs : s.im = T) :
    ‖logDeriv F s‖ ≤
      (∑' ρ : ℂ, localZeroMultiplicity F T ρ) / c +
        (6 + 10 * ‖(((3 : ℝ) : ℂ) + T * Complex.I) - s‖) *
          ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have hm := localZeroCount_bound_of_orderAtMostOne hε hfe hright hF h0 horder T
  have hn := summable_nearZeroResolvent_and_bound_of_avoiding_height hc ha hs hm.1
  have he :=
    (logDeriv_nearZero_error_le hε hfe hright hF h0 horder s
        (nonzero_at_avoiding_height hc ha hs)).2
  rw [hs] at he
  have htri :=
    norm_add_le (logDeriv F s - ∑' ρ : ℂ, nearZeroResolventTerm F T s ρ)
      (∑' ρ : ℂ, nearZeroResolventTerm F T s ρ)
  rw [sub_add_cancel] at htri
  linarith only [he, hn.2, htri]

/-- For a point of imaginary height T, its distance from 3+iT equals the
absolute real difference abs(3-Re s). Check the complex components and the
real norm. This makes the nearby-zero error uniform on a horizontal strip. -/
theorem norm_rightReference_sub_eq {s : ℂ} {T : ℝ} (hs : s.im = T) :
    ‖(((3 : ℝ) : ℂ) + T * Complex.I) - s‖ = |3 - s.re| := by
  have he : (((3 : ℝ) : ℂ) + T * Complex.I) - s = ((3 - s.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero]
      norm_num only
    · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, hs,
        sub_self]
  rw [he, Complex.norm_real, Real.norm_eq_abs]

/-- On a zero-avoiding height, for real part between minus one and two, the
completed logarithmic derivative is bounded by the local count divided by
the separation margin plus 46 times its norm at 3+iT. The reference distance
is at most four. This is uniform across the width of the horizontal edge. -/
theorem norm_logDeriv_horizontalStrip_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {T c : ℝ} (hc : 0 < c)
    (ha : ∀ ρ : ℂ, F ρ = 0 → c ≤ |T - ρ.im|) {s : ℂ} (hs : s.im = T) (hlo : -1 ≤ s.re)
    (hhi : s.re ≤ 2) :
    ‖logDeriv F s‖ ≤
      (∑' ρ : ℂ, localZeroMultiplicity F T ρ) / c +
        46 * ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have hb := norm_logDeriv_le_of_avoiding_height hε hfe hright hF h0 horder hc ha hs
  rw [norm_rightReference_sub_eq hs] at hb
  have hn : |3 - s.re| ≤ 4 := abs_le.mpr ⟨by linarith only [hhi], by linarith only [hlo]⟩
  have hh :=
    mul_le_mul_of_nonneg_right hn (norm_nonneg (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)))
  nlinarith only [hb, hh]

/-- Entire order-one completion data admit in every unit height interval
an entire horizontal segment with real part between minus one and two on
which the function is nonzero and the logarithmic derivative has an explicit
local-count bound. Select a height separated from all zeros, then apply the
uniform strip estimate. This connects good-height selection to the actual
horizontal-edge integrand bound required in an explicit-formula proof. -/
theorem exists_height_with_horizontalStrip_bound {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (H : ℝ) :
    ∃ T ∈ Set.Icc H (H + 1),
      ∀ s : ℂ,
        s.im = T →
          -1 ≤ s.re →
          s.re ≤ 2 →
          F s ≠ 0 ∧
            ‖logDeriv F s‖ ≤
              (∑' ρ : ℂ, localZeroMultiplicity F T ρ) /
                  (1 /
                    (4 *
                      (1 + (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
                        ∑' z : ℂ, localZeroMultiplicity F (H + 1) z))) +
                46 * ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ := by
  obtain ⟨T, hT, ha⟩ := exists_height_avoiding_zeros_of_orderAtMostOne hε hfe hright hF h0 horder H
  have hc :
    0 <
      1 /
        (4 *
          (1 + (∑' z : ℂ, localZeroMultiplicity F (H - 1) z) +
            ∑' z : ℂ, localZeroMultiplicity F (H + 1) z)) := by
    apply div_pos zero_lt_one
    have hm : 0 ≤ ∑' z : ℂ, localZeroMultiplicity F (H - 1) z :=
      tsum_nonneg (localZeroMultiplicity_nonneg F (H - 1))
    have hp : 0 ≤ ∑' z : ℂ, localZeroMultiplicity F (H + 1) z :=
      tsum_nonneg (localZeroMultiplicity_nonneg F (H + 1))
    nlinarith only [hm, hp]
  refine ⟨T, hT, ?_⟩
  intro s hs hlo hhi
  exact
    ⟨nonzero_at_avoiding_height hc ha hs,
      norm_logDeriv_horizontalStrip_le hε hfe hright hF h0 horder hc ha hs hlo hhi⟩

end PseudoPrime.AnalyticNumberTheory.General
