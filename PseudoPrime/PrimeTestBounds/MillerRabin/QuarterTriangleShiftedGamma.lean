/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularGammaWeightSeries
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleTranslatedBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleCentralGamma

/-! # Translated gamma-factor bound for even characters -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Outside the logarithmic support the cosine-modulated mass vanishes.
Take real parts in triangular Mellin inversion at scale exp(v). -/
theorem triangle_translated_mass_zero {a v : ℝ} (ha : 0 < a) (hv : 2 * a ≤ v) :
    (∫ t : ℝ, ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ * Real.cos (v * t)) = 0 := by
  let F (t : ℝ) :=
    Analysis.triangularMellinFunction a (Complex.I * t) * ((Real.exp v : ℝ) : ℂ) ^ (Complex.I * t)
  have hi : MeasureTheory.Integrable F :=
    LLS.PaperStatements.integrable_triangular_central_kernel_power ha (Real.exp_pos v)
  have h := LLS.PaperStatements.triangular_central_kernelIntegral_eq_profile ha (Real.exp_pos v)
  unfold LLS.PaperStatements.triangularKernelProfile at h
  rw [Real.log_exp, abs_of_nonneg (by linarith only [ha, hv]), max_eq_left (sub_nonpos.mpr hv),
    Complex.ofReal_zero] at h
  have hz : (∫ t : ℝ, F t) = 0 :=
    (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr (by positivity))
  have he (t : ℝ) :
    (F t).re = ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ * Real.cos (v * t) := by
    unfold F
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'), ←
      Complex.ofReal_log (Real.exp_pos v).le, Real.log_exp,
      show (v : ℂ) * (Complex.I * t) = ((v * t : ℝ) : ℂ) * Complex.I by
        push_cast; ring,
      Analysis.norm_triangularMellinFunction_imaginary ha.ne',
      Analysis.triangularMellinFunction_imaginary ha.ne', Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  simp_rw [← he]
  exact (integral_re hi).trans (congrArg Complex.re hz)

/-- For an even character and radius at least 287, the cosine-modulated full
gamma integrand satisfies the section 76 bound after its constant part cancels. -/
theorem triangle_translated_gamma_bound {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) {r : ℝ}
    (hradius : 287 ≤ r) :
    (2 / 5) *
          |∫ t : ℝ,
              (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                    Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re *
                Real.cos ((2 * Real.log r + 5 / 2) * t)| /
        Real.pi <
      1 / 250 := by
  let b : ℝ := 1 / 4
  have he (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re =
      (-Real.log Real.pi + (Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re) / 2 := by
    have hz : ((Complex.I * (t : ℂ) + 1 / 2) / 2) = (b : ℂ) + Complex.I * (t / 2) := by
      dsimp only [b]; push_cast; ring
    have hp : 0 < ((Complex.I * (t : ℂ) + 1 / 2) / 2).re := by
      rw [hz]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only [b]
    rw [AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma hχ
        (fun n => AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n),
      hz, ← Complex.ofReal_log Real.pi_pos.le]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
    ring
  let w := fun t : ℝ ↦ ‖Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)‖
  let B := (-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2
  let C := fun t : ℝ ↦
    (1 / 2 : ℝ) *
      ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
      w t
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < (5 / 4))
  have hw : MeasureTheory.Integrable w := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_line_in_strip K (c := 0)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only)
    simp only [Complex.ofReal_zero, zero_add] at h
    exact h.norm
  have hid (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re =
      B * w t + C t := by
    rw [Analysis.triangularMellinFunction_imaginary (by norm_num only : ((5 / 4) : ℝ) ≠ 0)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [he]
    dsimp only [B, C, w]
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : ((5 / 4) : ℝ) ≠ 0)]
    ring
  have hr :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re) := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1)
        (by norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) zero_lt_one
    simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
    exact Complex.reCLM.integrable_comp h
  have hc : MeasureTheory.Integrable C := by
    have h := hr.sub (hw.const_mul B)
    convert h using 1
    funext t
    change
      C t =
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re -
          B * w t
    rw [hid]
    ring
  let v := 2 * Real.log r + 5 / 2
  have hv : 2 * (5 / 4) ≤ v := by
    dsimp only [v]
    linarith only [Real.log_nonneg (show 1 ≤ r by linarith only [hradius])]
  have hm : (∫ t : ℝ, w t * Real.cos (v * t)) = 0 :=
    triangle_translated_mass_zero (by norm_num only) hv
  have hmod {f : ℝ → ℝ} (hf : MeasureTheory.Integrable f) :
    MeasureTheory.Integrable (fun t => f t * Real.cos (v * t)) :=
    hf.mul_bdd (c := 1) (by fun_prop)
      (Filter.Eventually.of_forall (fun t => (Real.norm_eq_abs _).trans_le (Real.abs_cos_le_one _)))
  have hid' (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re *
        Real.cos (v * t) =
      B * (w t * Real.cos (v * t)) + C t * Real.cos (v * t) := by
    rw [hid]; ring
  change (2 / 5) * |∫ t : ℝ, _ * Real.cos (v * t)| / Real.pi < _
  simp_rw [hid']
  rw [MeasureTheory.integral_add ((hmod hw).const_mul B) (hmod hc),
    MeasureTheory.integral_const_mul, hm, mul_zero, zero_add]
  simpa only [C, b, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    triangle_translated_error_bound hradius

end PseudoPrime.PrimeTestBounds.MillerRabin
