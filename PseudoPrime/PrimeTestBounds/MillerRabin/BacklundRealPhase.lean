/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundEulerLog
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogReal
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.LogFactor

/-! # Euler-normalized zeta phase on the real axis -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem xiLogFactor_im_ofReal {x : ℝ} (hx : 1 < x) :
    (AnalyticNumberTheory.RiemannXi.xiLogFactor (x : ℂ)).im = 0 := by
  have hx0 : 0 ≤ x := (lt_trans (by norm_num only : (0 : ℝ) < 1) hx).le
  have hx1 : 0 ≤ x - 1 := sub_nonneg.mpr hx.le
  have hx2 : 0 < x / 2 := div_pos (lt_trans (by norm_num only : (0 : ℝ) < 1) hx) (by norm_num only)
  have hg := AnalyticNumberTheory.Gamma.logGammaSeries_im_ofReal hx2
  unfold AnalyticNumberTheory.RiemannXi.xiLogFactor
  simp only [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_log hx0,
    ← Complex.ofReal_log hx1, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_mul,
    Complex.add_im, Complex.sub_im, Complex.ofReal_im, zero_add, sub_zero, hg]

private theorem coeff_bound (n : ℕ) :
    ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, abs_of_nonneg (Real.log_natCast_nonneg n)]
  by_cases hn : Real.log n = 0
  · rw [hn, div_zero]; norm_num only
  · have hp : 0 < Real.log n := lt_of_le_of_ne (Real.log_natCast_nonneg n) (Ne.symm hn)
    exact (div_le_one₀ hp).2 ArithmeticFunction.vonMangoldt_le_log

private theorem eulerLogTerm_im_ofReal (x : ℝ) (n : ℕ) :
    (LSeries.term (fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ)) (x : ℂ)
          n).im =
      0 := by
  rw [LSeries.term_def]
  by_cases hn : n = 0
  · simp only [hn, ↓reduceIte, Complex.zero_im]
  · simp only [hn, ↓reduceIte, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n),
      ← Complex.ofReal_div, Complex.ofReal_im]

/-- For real `x > 1`, the Euler-normalized logarithm of zeta has zero
imaginary part. Each Dirichlet-series term is real and the coefficient
bound supplies absolute convergence. This fixes the zero-count phase base. -/
theorem backlundZetaLog_im_ofReal {x : ℝ} (hx : 1 < x) :
    (AnalyticNumberTheory.RiemannZeta.backlundZetaLog (x : ℂ)).im = 0 := by
  have hs :
    LSeriesSummable (fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ))
      (x : ℂ) :=
    LSeriesSummable_of_bounded_of_one_lt_re (fun n _ ↦ coeff_bound n)
      (by simpa only [Complex.ofReal_re] using hx)
  change
    Summable
      (LSeries.term (fun n ↦ ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) / (Real.log n : ℂ))
        (x : ℂ)) at hs
  unfold AnalyticNumberTheory.RiemannZeta.backlundZetaLog LSeries
  rw [Complex.im_tsum hs]
  simp only [eulerLogTerm_im_ofReal, tsum_zero]

/-- In the half-plane `Re s > 1`, exponentiating the sum of the xi factor
logarithm and the Euler-normalized zeta logarithm gives `2 * xi(s)`. This
fixes the normalization used for the right vertical-edge argument. -/
theorem exp_xi_euler_log {s : ℂ} (hs : 1 < s.re) :
    Complex.exp
        (AnalyticNumberTheory.RiemannXi.xiLogFactor s +
          AnalyticNumberTheory.RiemannZeta.backlundZetaLog s) =
      2 * AnalyticNumberTheory.RiemannXi.riemannXi s := by
  have hs0 : 0 < s.re := lt_trans (by norm_num only) hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact (lt_irrefl (1 : ℝ)) hs
  rw [Complex.exp_add, AnalyticNumberTheory.RiemannZeta.exp_backlundZetaLog hs,
    AnalyticNumberTheory.RiemannXi.riemannXi_eq_exp_factor hs0 hs1]
  ring

private theorem polar_mul_factor (u z w : ℂ) (φ : ℝ)
    (hz : z = (‖z‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I))
    (hw : w = (1 / 2 : ℂ) * Complex.exp u * z) :
    w = (‖w‖ : ℂ) * Complex.exp (((u.im + φ : ℝ) : ℂ) * Complex.I) := by
  have he : Complex.exp u = (Real.exp u.re : ℂ) * Complex.exp ((u.im : ℂ) * Complex.I) := by
    conv_lhs => rw [← Complex.re_add_im u]
    rw [Complex.exp_add, Complex.ofReal_exp]
  have hn : ‖w‖ = (1 / 2 : ℝ) * Real.exp u.re * ‖z‖ := by
    rw [hw, norm_mul, norm_mul, Complex.norm_exp]
    norm_num only [norm_div, norm_one, Complex.norm_ofNat]
  rw [hn, hw, he]
  conv_lhs => rw [hz]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

/-- At positive real part away from one, a polar argument of zeta yields a
polar argument of xi by adding the imaginary part of the xi logarithmic
factor. The positive factor `1/2` leaves the phase unchanged. -/
theorem xi_polar_of_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (φ : ℝ)
    (hz : riemannZeta s = (‖riemannZeta s‖ : ℂ) * Complex.exp ((φ : ℂ) * Complex.I)) :
    AnalyticNumberTheory.RiemannXi.riemannXi s =
      (‖AnalyticNumberTheory.RiemannXi.riemannXi s‖ : ℂ) *
        Complex.exp
          ((((AnalyticNumberTheory.RiemannXi.xiLogFactor s).im + φ : ℝ) : ℂ) * Complex.I) := by
  exact polar_mul_factor _ _ _ φ hz (AnalyticNumberTheory.RiemannXi.riemannXi_eq_exp_factor hs hs1)

/-- At a real point greater than one, the combined xi-factor and Euler
zeta logarithm has imaginary part zero. Both constituent logarithms are
real there, fixing the base value of the vertical-edge phase. -/
theorem xi_euler_log_im_ofReal {x : ℝ} (hx : 1 < x) :
    (AnalyticNumberTheory.RiemannXi.xiLogFactor (x : ℂ) +
          AnalyticNumberTheory.RiemannZeta.backlundZetaLog (x : ℂ)).im =
      0 := by
  rw [Complex.add_im, xiLogFactor_im_ofReal hx, backlundZetaLog_im_ofReal hx, add_zero]

end PseudoPrime.PrimeTestBounds.MillerRabin
