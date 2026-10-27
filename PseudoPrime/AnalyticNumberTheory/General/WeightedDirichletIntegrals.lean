/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Weighted Dirichlet-series integration along continuous vertical heights -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A Dirichlet-series term at sigma+it has the same norm as at real sigma.
Evaluate the term norm using the real part. This supplies a height-independent coefficient. -/
theorem norm_LSeries_term_vertical (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term f ((σ : ℂ) + Complex.I * t) n‖ = ‖LSeries.term f (σ : ℂ) n‖ := by
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

/-- For fixed coefficient index and real sigma, the Dirichlet-series term is continuous
in imaginary height. Separate the zero index and use the nonzero complex power otherwise.
This provides regularity before multiplication by an integrable weight. -/
theorem continuous_LSeries_term_vertical (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ ↦ LSeries.term f ((σ : ℂ) + Complex.I * t) n) := by
  by_cases hn : n = 0
  · simp only [LSeries.term, hn, ite_true]
    exact continuous_const
  · simp only [LSeries.term, ite_eq_right hn]
    have hz : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have hP : Continuous (fun t : ℝ ↦ (n : ℂ) ^ ((σ : ℂ) + Complex.I * t)) :=
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).const_cpow (Or.inl hz)
    exact
      continuous_const.div hP
        (fun t ↦ by
          rw [Ne, Complex.cpow_eq_zero_iff]
          exact fun he ↦ hz he.1)

/-- For a continuous real height function and integrable complex weight, each
weighted Dirichlet-series term is integrable. Its norm is a fixed coefficient times the
weight norm. This works for reflected heights without a special Mellin-kernel structure. -/
theorem integrable_LSeries_term_mul_weight (f : ℕ → ℂ) (σ : ℝ) (n : ℕ) (T : ℝ → ℝ)
    (hT : Continuous T) (W : ℝ → ℂ) (hiW : MeasureTheory.Integrable W) :
    MeasureTheory.Integrable (fun t : ℝ ↦ LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t) := by
  apply
    (hiW.norm.const_mul ‖LSeries.term f (σ : ℂ) n‖).mono'
      (((continuous_LSeries_term_vertical f σ n).comp hT).aestronglyMeasurable.mul
        hiW.aestronglyMeasurable)
  exact
    MeasureTheory.ae_of_all _
      (fun t ↦ by
        change ‖LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t‖ ≤ _
        rw [norm_mul, norm_LSeries_term_vertical])

/-- Absolute Dirichlet convergence at real sigma makes the integrated term norms summable
for any height function and weight. Factor out the constant norm of each coefficient.
This is the absolute-convergence premise for the weighted integral exchange. -/
theorem summable_integral_norm_LSeries_term_mul_weight {f : ℕ → ℂ} {σ : ℝ}
    (hs : LSeriesSummable f (σ : ℂ)) (T : ℝ → ℝ) (W : ℝ → ℂ) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t‖) := by
  have h := hs.norm.mul_right (∫ t : ℝ, ‖W t‖)
  apply h.congr
  intro n
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  exact
    MeasureTheory.ae_of_all _
      (fun t ↦ by
        change
          ‖LSeries.term f (σ : ℂ) n‖ * ‖W t‖ = ‖LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t‖
        rw [norm_mul, norm_LSeries_term_vertical])

/-- For absolute Dirichlet convergence, a continuous real height function and
integrable complex weight, exchange the full Dirichlet series with integration.
Use termwise integrability and summable integral norms. This kernel-independent interface
supports both ordinary and reflected Mellin lines. -/
theorem integral_LSeries_mul_weight_eq_tsum {f : ℕ → ℂ} {σ : ℝ} (hs : LSeriesSummable f (σ : ℂ))
    (T : ℝ → ℝ) (W : ℝ → ℂ) (hT : Continuous T) (hiW : MeasureTheory.Integrable W) :
    (∫ t : ℝ, LSeries f ((σ : ℂ) + Complex.I * T t) * W t) =
      ∑' n : ℕ, ∫ t : ℝ, LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t := by
  have he (t : ℝ) :
    LSeries f ((σ : ℂ) + Complex.I * T t) * W t =
      ∑' n : ℕ, LSeries.term f ((σ : ℂ) + Complex.I * T t) n * W t := by
    rw [tsum_mul_right]
    rfl
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he)]
  exact
    (MeasureTheory.integral_tsum_of_summable_integral_norm
        (fun n ↦ integrable_LSeries_term_mul_weight f σ n T hT W hiW)
        (summable_integral_norm_LSeries_term_mul_weight hs T W)).symm

end PseudoPrime.AnalyticNumberTheory.General
