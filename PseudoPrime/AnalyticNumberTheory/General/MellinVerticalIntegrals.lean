/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestStripDecay
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestAnalytic
public import PseudoPrime.AnalyticNumberTheory.General.VerticalLogDerivativeGrowth
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrable vertical Mellin logarithmic derivatives

Linear completed-logarithmic growth and cubic Mellin decay supply an integrable
majorant on both sides of the residue contour.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- If a complex factor has linear height growth and a second factor has bounded
zeroth and cubic height moments, their product is bounded by an explicit
constant times (1+T^2) inverse. Expand (1+abs(T))(1+T^2) and use the
nonnegative factor (abs(T)-1)^2. This majorant is integrable on the real line. -/
private theorem linear_growth_cubic_decay_bound (L W : ℂ) (A D₀ D₃ T : ℝ) (hA : 0 ≤ A)
    (hL : ‖L‖ ≤ A * (1 + |T|)) (h₀ : ‖W‖ ≤ D₀) (h₃ : |T| ^ 3 * ‖W‖ ≤ D₃) :
    ‖L * W‖ ≤ (A * (2 * D₀ + 2 * D₃)) * (1 + T ^ 2)⁻¹ := by
  have hp :=
    mul_nonneg (sq_nonneg (|T| - 1))
      (mul_nonneg (add_nonneg (abs_nonneg T) zero_le_one) (norm_nonneg W))
  have hw : (1 + |T|) * (1 + |T| ^ 2) * ‖W‖ ≤ 2 * D₀ + 2 * D₃ := by nlinarith only [hp, h₀, h₃]
  have hh :=
    mul_le_mul_of_nonneg_right hL
      (mul_nonneg (norm_nonneg W) (add_nonneg zero_le_one (sq_nonneg T)))
  have ha := mul_le_mul_of_nonneg_left hw hA
  have hb : ‖L * W‖ * (1 + T ^ 2) ≤ A * (2 * D₀ + 2 * D₃) := by
    rw [norm_mul]
    rw [sq_abs] at ha
    nlinarith only [hh, ha]
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg T))).mpr
  exact hb

/-- For an entire function with a zero-free vertical line and a linear
logarithmic derivative bound there, multiplication by the Mellin transform
of an even smooth compact logarithmic test gives an integrable vertical
function. Continuity supplies measurability, and zeroth and cubic Mellin
bounds give a constant multiple of (1+T^2) inverse. This justifies whole-line
limits of the finite contour's vertical edges. -/
theorem integrable_vertical_logDeriv_mellin {F : ℂ → ℂ} (hF : Differentiable ℂ F) (σ A : ℝ)
    (hA : 0 ≤ A) (hzero : ∀ T : ℝ, F ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hbound : ∀ T : ℝ, ‖logDeriv F ((σ : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|)) (g : ℝ → ℂ)
    (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    MeasureTheory.Integrable
      (fun T : ℝ ↦
        logDeriv F ((σ : ℂ) + T * Complex.I) *
          mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)) := by
  obtain ⟨D₀, _, h₀⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg σ σ 0
  obtain ⟨D₃, _, h₃⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg σ σ 3
  have hline : Continuous (fun T : ℝ ↦ (σ : ℂ) + T * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hlog : Continuous (fun T : ℝ ↦ logDeriv F ((σ : ℂ) + T * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro T
    have ha : ContinuousAt (logDeriv F) ((σ : ℂ) + T * Complex.I) :=
      ((hF.analyticAt _).deriv.div (hF.analyticAt _) (hzero T)).continuousAt
    exact ha.comp (f := fun T : ℝ ↦ (σ : ℂ) + T * Complex.I) hline.continuousAt
  have hm := (differentiable_mellin_logarithmicTestWeight g hc hg.continuous).continuous
  apply
    (integrable_inv_one_add_sq.const_mul (A * (2 * D₀ + 2 * D₃))).mono'
      (hlog.mul (hm.comp hline)).aestronglyMeasurable
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      have h₀' := h₀ σ ⟨le_refl σ, le_refl σ⟩ T
      simp only [pow_zero, one_mul] at h₀'
      exact
        linear_growth_cubic_decay_bound _ _ A D₀ D₃ T hA (hbound T) h₀'
          (h₃ σ ⟨le_refl σ, le_refl σ⟩ T)

/-- For general completion data with admissible complex gamma shifts, entire
order-one regularization nonzero at zero, conjugate functional equation and
right-half-plane nonvanishing, both outer logarithmic Mellin integrands are
integrable. Coefficient bounds and the reference-line series give linear
growth at real parts two and minus one. The functional equation excludes
zeros on the left line, and compact-test Mellin decay supplies integrability.
This removes separate vertical-integrability premises from the zero-side identity. -/
theorem integrable_outer_logDeriv_mellin_of_completion {F L : ℂ → ℂ} {ε : ℂ} {q d : ℕ} (hq : 1 ≤ q)
    (k : ℤ) (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    (hε : ε ≠ 0) (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) {a : ℕ → ℂ}
    (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I))
    (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) :
    MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv F (((2 : ℝ) : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) (((2 : ℝ) : ℂ) + T * Complex.I)) ∧
      MeasureTheory.Integrable
        (fun T : ℝ ↦
          logDeriv F (((-1 : ℝ) : ℂ) + T * Complex.I) *
            mellin (logarithmicTestWeight g) (((-1 : ℝ) : ℂ) + T * Complex.I)) := by
  obtain ⟨A, hA, hb⟩ :=
    exists_vertical_logDeriv_linear_bound_of_completion hq k κ hκ hreg hε hfe hright hF h0 horder ha
      hL hdL hlog
  have hzero : ∀ T : ℝ, F (((2 : ℝ) : ℂ) + T * Complex.I) ≠ 0 := by
    intro T
    apply hright
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have hleft : ∀ T : ℝ, F (((-1 : ℝ) : ℂ) + T * Complex.I) ≠ 0 := by
    intro T hz
    have hs := zero_re_mem_Icc_of_functionalEquation hε hfe hright hz
    have hre : ((((-1 : ℝ) : ℂ) + T * Complex.I)).re = -1 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    rw [hre] at hs
    linarith only [hs.1]
  exact
    ⟨integrable_vertical_logDeriv_mellin hF 2 A hA.le hzero (fun T ↦ (hb T).1) g he hc hg,
      integrable_vertical_logDeriv_mellin hF (-1) A hA.le hleft (fun T ↦ (hb T).2) g he hc hg⟩

end PseudoPrime.AnalyticNumberTheory.General
