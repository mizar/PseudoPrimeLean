/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedPhase
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftZeta

/-! # Zeta contributions in the section 107 phase bound -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For each nonnegative frequency the xi contour is bounded in absolute value
by the sixth-pole zeta mass, since the cosine factor has absolute value at most one. -/
theorem weighted_xi_contour_abs (hRH : RiemannHypothesis) {s : ℝ} (hs : 0 ≤ s) :
    |twoShiftXiContourValue s| ≤ ∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖ := by
  have hsum :=
    LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm twoShiftSymmetricMellin hRH
      (Real.exp_pos s)
  have h :=
    (congrArg Complex.re (twoShift_symmetric_xi_contour hRH hs)).symm.trans (Complex.re_tsum hsum)
  unfold twoShiftXiContourValue
  rw [h]
  have he (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    (twoShiftSymmetricMellin.zetaOscillatingZeroTerm (Real.exp s) ρ).re =
      ‖quarterKernel570.zetaKernelZeroTerm ρ‖ * Real.cos (s * (ρ : ℂ).im) := by
    dsimp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm,
      LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm]
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, norm_mul, Complex.norm_natCast]
    change ((_ * twoShiftSymmetricKernel (Complex.I * (ρ : ℂ).im)) * _).re = _
    rw [twoShift_symmetric_axis, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, twoShift_exp_axis, quarter_zero_norm_570]
  simp only [he]
  rw [← Real.norm_eq_abs]
  have hm :=
    (LLS.PaperStatements.MellinKernel.summable_zetaKernelZeroTerm quarterKernel570 hRH).norm
  have hp (ρ : AnalyticNumberTheory.RiemannXi.Zero) :
    ‖‖quarterKernel570.zetaKernelZeroTerm ρ‖ * Real.cos (s * (ρ : ℂ).im)‖ ≤
      ‖quarterKernel570.zetaKernelZeroTerm ρ‖ := by
    rw [norm_mul, norm_norm, Real.norm_eq_abs]
    exact
      mul_le_of_le_one_right (norm_nonneg _) (abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  have hcos := hm.of_norm_bounded hp
  exact (norm_tsum_le_tsum_norm hcos.norm).trans (hcos.norm.tsum_le_tsum hp hm)

/-- For the section 107 coefficients, a bound m on the sixth-pole zeta mass
bounds the four-frequency xi contribution from below. -/
theorem weighted_xi_cosine_lower (hRH : RiemannHypothesis) {m : ℝ}
    (hm : (∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖) ≤ m) :
    let u : ℝ := 11 / 25
    let v : ℝ := 91 / 200
    (-(3 * (u + v + (u + v) ^ 2 / 2) * m)) ≤
      3 *
        (u * twoShiftXiContourValue (14 / 5) - v * twoShiftXiContourValue 3 -
            ((u ^ 2 + v ^ 2) / 2) * twoShiftXiContourValue 0 +
          (u * v) * twoShiftXiContourValue (1 / 5)) := by
  intro u v
  have h (s : ℝ) (hs : 0 ≤ s) := abs_le.mp ((weighted_xi_contour_abs hRH hs).trans hm)
  dsimp only [u, v]
  linarith only [(h (14 / 5) (by norm_num only)).1, (h 3 (by norm_num only)).2, (h 0 (le_refl 0)).2,
    (h (1 / 5) (by norm_num only)).1]

/-- The real oscillating zeta term at any positive scale is bounded by the
same sixth-pole mass as the fixed-frequency xi contours. -/
theorem weighted_zeta_osc_abs (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x) :
    |(∑' ρ, quarterKernel570.zetaOscillatingZeroTerm x ρ).re| ≤
      ∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖ := by
  have h :=
    (LLS.PaperStatements.MellinKernel.summable_zetaOscillatingZeroTerm quarterKernel570 hRH hx).norm
  apply (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm h).trans ?_)
  rw [tsum_congr
      (LLS.PaperStatements.MellinKernel.norm_zetaOscillatingZeroTerm quarterKernel570 hx)]

/-- A common sixth-pole zeta mass bound controls the fixed cosine and shifted
oscillating zeta contributions in the section 107 comparison. -/
theorem weighted_zeta_total_lower (hRH : RiemannHypothesis) {x y m : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hm : (∑' ρ, ‖quarterKernel570.zetaKernelZeroTerm ρ‖) ≤ m) :
    let u : ℝ := 11 / 25
    let v : ℝ := 91 / 200
    let Z := fun t : ℝ ↦ (∑' ρ, quarterKernel570.zetaOscillatingZeroTerm t ρ).re
    (-(3 * (2 * (u + v) + (u + v) ^ 2 / 2) * m)) ≤
      3 *
        (u * (twoShiftXiContourValue (14 / 5) + Z x) - v * (twoShiftXiContourValue 3 + Z y) -
            ((u ^ 2 + v ^ 2) / 2) * twoShiftXiContourValue 0 +
          (u * v) * twoShiftXiContourValue (1 / 5)) := by
  intro u v Z
  have h := weighted_xi_cosine_lower hRH hm
  have hX := (abs_le.mp ((weighted_zeta_osc_abs hRH hx).trans hm)).1
  have hY := (abs_le.mp ((weighted_zeta_osc_abs hRH hy).trans hm)).2
  dsimp only [u, v, Z] at h ⊢
  linarith only [h, hX, hY]

end PseudoPrime.PrimeTestBounds.MillerRabin
