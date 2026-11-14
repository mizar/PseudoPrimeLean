/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase

/-! # Derivatives of critical-line phase terms -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A constant multiple of a real-frequency exponential divided by a
constant has the displayed real derivative. This supplies both derivatives
of each term in the finite critical-line phase sum. -/
theorem hasDerivAt_re_phase_term (g v : ℝ) (c d : ℂ) :
    HasDerivAt (fun v : ℝ ↦ (c * Complex.exp (((g * v : ℝ) : ℂ) * Complex.I) / d).re)
      ((c * ((g : ℂ) * Complex.I) * Complex.exp (((g * v : ℝ) : ℂ) * Complex.I) / d).re) v := by
  have he :
    HasDerivAt (fun v : ℝ ↦ Complex.exp (((g * v : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((g * v : ℝ) : ℂ) * Complex.I) * ((g : ℂ) * Complex.I)) v := by
    have h := (((hasDerivAt_id (v : ℂ)).mul_const ((g : ℂ) * Complex.I)).cexp).comp_ofReal
    convert h using 1
    · funext u
      congr 1
      simp only [Complex.ofReal_mul, id_eq]
      ring
    · simp only [Complex.ofReal_mul, id_eq, one_mul]
      congr 2
      ring
  have h := (he.const_mul c).div_const d
  have h' := (hasDerivAt_const v Complex.reCLM).clm_apply h
  convert h' using 1
  · rfl
  · simp only [zero_apply, zero_add, Complex.reCLM_apply]
    congr 1
    ring

/-- The first derivative of the finite low-zero phase sum, obtained by
multiplying each exponential term by its imaginary frequency. -/
noncomputable def zeroHeadPhaseDeriv {n : ℕ} (g : Fin n → ℝ) (v : ℝ) : ℝ :=
  2 *
    ∑ i,
      (((g i : ℂ) * Complex.I) * Complex.exp (((g i * v : ℝ) : ℂ) * Complex.I) /
          (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)).re

/-- The second derivative of the finite low-zero phase sum, obtained by
multiplying each exponential term by the square of its imaginary frequency. -/
noncomputable def zeroHeadPhaseDeriv2 {n : ℕ} (g : Fin n → ℝ) (v : ℝ) : ℝ :=
  2 *
    ∑ i,
      (((g i : ℂ) * Complex.I) * ((g i : ℂ) * Complex.I) *
            Complex.exp (((g i * v : ℝ) : ℂ) * Complex.I) /
          (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I)).re

/-- The finite phase sum has the displayed first derivative at every real
point. Differentiate each term and commute the finite sum with real part. -/
theorem hasDerivAt_zeroHeadPhase {n : ℕ} (g : Fin n → ℝ) (v : ℝ) :
    HasDerivAt (zeroHeadPhase g) (zeroHeadPhaseDeriv g v) v := by
  have h :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ hasDerivAt_re_phase_term (g i) v 1 (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I))
  have h' := h.const_mul 2
  convert h' using 1
  · funext y
    simp only [zeroHeadPhase, Complex.re_sum, one_mul]
  · simp only [zeroHeadPhaseDeriv, one_mul]

/-- The first derivative of the finite phase sum has the displayed second
derivative at every real point, by termwise differentiation. -/
theorem hasDerivAt_zeroHeadPhaseDeriv {n : ℕ} (g : Fin n → ℝ) (v : ℝ) :
    HasDerivAt (zeroHeadPhaseDeriv g) (zeroHeadPhaseDeriv2 g v) v := by
  have h :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦
        hasDerivAt_re_phase_term (g i) v ((g i : ℂ) * Complex.I)
          (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I))
  have h' := h.const_mul 2
  convert h' using 1
  · rfl
  · rfl

/-- The absolute second derivative of one normalized phase term is at most
the absolute ordinate. The exponential has norm one and the imaginary part
of the critical-line denominator supplies the lower bound on its norm. -/
theorem abs_phase_term_deriv2_le (g v : ℝ) :
    |(((g : ℂ) * Complex.I) * ((g : ℂ) * Complex.I) * Complex.exp (((g * v : ℝ) : ℂ) * Complex.I) /
            (((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I)).re| ≤
      |g| := by
  have hden : |g| ≤ ‖((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I‖ := by
    have h := Complex.abs_im_le_norm (((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I)
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, zero_add, add_zero] using h
  have hexp : ‖Complex.exp (((g * v : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, Real.exp_zero]
  have hg : ‖(g : ℂ) * Complex.I‖ = |g| := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
  calc
    _ ≤
        ‖((g : ℂ) * Complex.I) * ((g : ℂ) * Complex.I) *
              Complex.exp (((g * v : ℝ) : ℂ) * Complex.I) /
            (((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I)‖ :=
      Complex.abs_re_le_norm _
    _ = |g| * |g| / ‖((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I‖ := by
      rw [norm_div, norm_mul, norm_mul, hg, hexp, mul_one]
    _ ≤ |g| := by
      by_cases h : |g| = 0
      · simp only [h, zero_mul, zero_div, le_refl]
      · have hp : 0 < |g| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h)
        have hd : 0 < ‖((1 / 2 : ℝ) : ℂ) + (g : ℂ) * Complex.I‖ := hp.trans_le hden
        exact (div_le_iff₀ hd).2 (mul_le_mul_of_nonneg_left hden (abs_nonneg _))

/-- The absolute second derivative of the finite phase sum is at most twice
the sum of absolute ordinates. This uniform bound supports interpolation
between certified phase-grid endpoints. -/
theorem abs_zeroHeadPhaseDeriv2_le {n : ℕ} (g : Fin n → ℝ) (v : ℝ) :
    |zeroHeadPhaseDeriv2 g v| ≤ 2 * ∑ i, |g i| := by
  simp only [zeroHeadPhaseDeriv2, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  exact
    (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
      (Finset.sum_le_sum (fun i _ ↦ abs_phase_term_deriv2_le (g i) v))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
