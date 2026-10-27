/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogarithmicBounds

/-! # Explicit pole-distance bounds on variable completed contour lines -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- On the positive strip 1/2<=Re(s)<=3, bound the full GammaReal logarithmic derivative
by 11+abs(Im(s)). Use the shifted digamma bound and elementary norm estimates.
This common strip contains both parity arguments needed for variable contour lines. -/
theorem norm_logDeriv_GammaReal_positive_strip_le_eleven {s : ℂ} (hl : 1 / 2 ≤ s.re)
    (hu : s.re ≤ 3) : ‖logDeriv Complex.Gammaℝ s‖ ≤ 11 + |s.im| := by
  have hp : 0 < s.re := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hl
  have hr : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      half_add_ne_neg_nat_of_re_pos hp (a := 0) le_rfl
  have hz : (1 / 4 : ℝ) ≤ (s / 2).re := by
    rw [Complex.div_ofNat_re]
    linarith only [hl]
  have hd := Gamma.norm_digamma_le_linear_of_re_ge (by norm_num only : (0 : ℝ) < 1 / 4) hz
  norm_num only at hd
  have hn := Complex.norm_le_abs_re_add_abs_im (s / 2)
  simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, abs_div, abs_of_nonneg hp.le,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at hn
  have hlog := Real.log_le_sub_one_of_pos Real.pi_pos
  have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
    linarith only [hlog, Real.pi_lt_four]
  rw [logDeriv_Gammaℝ_of_half_ne_neg_nat hr]
  have hnorm := norm_add_le (-(Complex.log (Real.pi : ℂ)) / 2) (Complex.digamma (s / 2) / 2)
  simp only [norm_div, norm_neg, Complex.norm_two] at hnorm
  nlinarith only [hnorm, hd, hn, hnlog, hu, Real.pi_lt_four, Gamma.digammaLogErrorBound_le_eight,
    abs_nonneg s.im]

/-- On 1/2<=Re(s)<=2, each character Gamma-factor logarithmic derivative has norm at most
11+abs(Im(s)). Reduce the two parity cases to the GammaReal strip estimate.
The bound is independent of character and modulus. -/
theorem norm_logDeriv_gammaFactor_positive_strip_le_linear {q : ℕ} (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hl : 1 / 2 ≤ s.re) (hu : s.re ≤ 2) : ‖logDeriv χ.gammaFactor s‖ ≤ 11 + |s.im| := by
  have hp : 0 < s.re := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hl
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ hp with he | he
  · rw [he, hf]
    exact norm_logDeriv_GammaReal_positive_strip_le_eleven hl (by linarith only [hu])
  · rw [he, hf]
    have hr :=
      norm_logDeriv_GammaReal_positive_strip_le_eleven (s := s + 1)
        (by
          rw [Complex.add_re, Complex.one_re]; linarith only [hl])
        (by
          rw [Complex.add_re, Complex.one_re]; linarith only [hu])
    simpa only [Complex.add_im, Complex.one_im, add_zero] using hr

/-- On 1/2<=Re(s)<=2, the Gamma-factor logarithmic derivative has norm at most
12+log(4+abs(Im(s)))/2. Combine the high-height logarithmic bound with the compact bound.
This explicit envelope is integrable against inverse-square kernel decay. -/
theorem norm_logDeriv_gammaFactor_positive_strip_le_log {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hl : 1 / 2 ≤ s.re) (hu : s.re ≤ 2) :
    ‖logDeriv χ.gammaFactor s‖ ≤ 12 + Real.log (4 + |s.im|) / 2 := by
  have hlog : 0 ≤ Real.log (4 + |s.im|) := Real.log_nonneg (by linarith only [abs_nonneg s.im])
  by_cases ht : 1 ≤ |s.im|
  · have hsr : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith only [hl], hu⟩
    have hb := norm_logDeriv_gammaFactor_le_log χ hsr ht
    have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
      rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
      have hp := Real.log_le_sub_one_of_pos Real.pi_pos
      linarith only [hp, Real.pi_lt_four]
    linarith only [hb, hnlog, Real.pi_lt_four, Gamma.digammaLogErrorBound_le_eight]
  · have hb := norm_logDeriv_gammaFactor_positive_strip_le_linear χ hl hu
    have ht1 : |s.im| ≤ 1 := (lt_of_not_ge ht).le
    linarith only [hb, ht1, hlog]

/-- For nonprincipal characters and 1<sigma<=2, bound the completed logarithmic derivative
by (sigma-1)^(-2)+(sigma-1)^(-1)+12+log(4+abs(t))/2.
Separate the ordinary Euler series and Gamma factor, using their explicit bounds.
This retains the distance from the pole instead of an unspecified strip constant. -/
theorem norm_logDeriv_completed_right_strip_le_gap_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) (hσu : σ ≤ 2) (t : ℝ) :
    ‖logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)‖ ≤
      (σ - 1)⁻¹ ^ 2 + (σ - 1)⁻¹ + 12 + Real.log (4 + |t|) / 2 := by
  let s : ℂ := (σ : ℂ) + Complex.I * t
  have hr : s.re = σ := by
    simp only [s, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hi : s.im = t := by
    simp only [s, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, one_mul, zero_mul, zero_add]
  have hr1 : 1 ≤ s.re := by
    rw [hr]; exact hσ.le
  have hp : 0 < s.re := zero_lt_one.trans_le hr1
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr1) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have ho := norm_logDeriv_le_inv_gap χ hσ t
  rw [mul_comm (t : ℂ) Complex.I] at ho
  have hg :=
    norm_logDeriv_gammaFactor_positive_strip_le_log χ
      (by
        rw [hr]; linarith only [hσ])
      (by
        rw [hr]; exact hσu)
  rw [hi] at hg
  have hc :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]; ring
  change ‖logDeriv χ.completedLFunction s‖ ≤ _
  rw [hc]
  have hn := norm_add_le (logDeriv χ.LFunction s) (logDeriv χ.gammaFactor s)
  linarith only [hn, ho, hg]

/-- For primitive nonprincipal characters with nonprincipal inverse and 0<e<=1, the
completed logarithmic derivative on Re(s)=-e is at most norm(log(q)) plus
e^(-2)+e^(-1)+12+log(4+abs(t))/2. Reflect to 1+e and apply the right-strip bound.
This explicit left-line envelope is unconditional and tracks the pole distance. -/
theorem norm_logDeriv_completed_left_strip_le_gap_log {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {e : ℝ}
    (he : 0 < e) (heu : e ≤ 1) (t : ℝ) :
    ‖logDeriv χ.completedLFunction ((-e : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.log (q : ℂ)‖ + e⁻¹ ^ 2 + e⁻¹ + 12 + Real.log (4 + |t|) / 2 := by
  let s : ℂ := ((1 + e : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have hr : 1 ≤ s.re := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [he]
  have hf :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs_eq : 1 - s = (-e : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  rw [hs_eq] at hf
  have hn := norm_add_le (Complex.log (q : ℂ)) (logDeriv χ⁻¹.completedLFunction s)
  rw [← hf, norm_neg] at hn
  have hb :=
    norm_logDeriv_completed_right_strip_le_gap_log hinv (σ := 1 + e) (by linarith only [he])
      (by linarith only [heu]) (-t)
  have hg : (1 + e : ℝ) - 1 = e := by ring
  rw [hg, abs_neg] at hb
  exact
    hn.trans
      (by
        dsimp only [s]; linarith only [hb])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
