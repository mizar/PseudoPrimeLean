/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaVerticalNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedLogDerivativeNumericalBounds
public import PseudoPrime.LLS.GammaKernel
public import PseudoPrime.LLS.MellinKernelLeftBounds

/-! # Explicit left completed integral for the Gamma kernel

The fixed line -9/16 reflects the completed logarithmic derivative to 17/16.
Numerical derivative and Gamma decay bounds yield a rational integrable envelope.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A nonnegative height envelope with bounds g≤32 and ga^4≤6 controls
g(L+283+a)(1+a²) by 20000(L+1), for L,a≥0.
Split at height one and use the uniform bound on the compact part and quartic decay
on the tail. This rational comparison supplies the left-integral majorant. -/
private theorem gamma_left_envelope {L a g : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hg : 0 ≤ g)
    (hg32 : g ≤ 32) (hg4 : g * a ^ 4 ≤ 6) : g * (L + 283 + a) * (1 + a ^ 2) ≤ 20000 * (L + 1) := by
  by_cases ha1 : a ≤ 1
  · have hfac : L + 283 + a ≤ 284 * (L + 1) := by nlinarith only [hL, ha1]
    have ha2 : 1 + a ^ 2 ≤ 2 := by nlinarith only [ha1, ha, sq_nonneg a]
    have hm :=
      mul_le_mul hg32 hfac (by linarith only [hL, ha] : 0 ≤ L + 283 + a)
        (by norm_num only : (0 : ℝ) ≤ 32)
    have hm2 :=
      mul_le_mul hm ha2 (by nlinarith only [sq_nonneg a])
        (by nlinarith only [hL] : 0 ≤ 32 * (284 * (L + 1)))
    nlinarith only [hm2, hL]
  · have ha1' : 1 ≤ a := (lt_of_not_ge ha1).le
    have hLa := mul_nonneg hL (sub_nonneg.mpr ha1')
    have hfac : L + 283 + a ≤ 284 * (L + 1) * a := by nlinarith only [hLa, ha1', hL]
    have hp : a * (1 + a ^ 2) ≤ 2 * a ^ 4 := by
      nlinarith only [ha1', sq_nonneg (a - 1), mul_nonneg (sub_nonneg.mpr ha1') (sq_nonneg a),
        mul_nonneg (sub_nonneg.mpr ha1') (pow_nonneg ha 3)]
    calc
      _ ≤ g * (284 * (L + 1) * a) * (1 + a ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfac hg)
          (by nlinarith only [sq_nonneg a])
      _ = 284 * (L + 1) * g * (a * (1 + a ^ 2)) := by ring
      _ ≤ 284 * (L + 1) * g * (2 * a ^ 4) :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (by nlinarith only [hL] : 0 ≤ 284 * (L + 1)) hg)
      _ = 568 * (L + 1) * (g * a ^ 4) := by ring
      _ ≤ 568 * (L + 1) * 6 := mul_le_mul_of_nonneg_left hg4 (by nlinarith only [hL])
      _ ≤ _ := by nlinarith only [hL]

/-- For primitive nonprincipal data with nonprincipal inverse and x>0,
the Gamma left-line integrand at a=-9/16 is bounded by
20000(log(q)+1)x^a/(1+t²). Reflect the completed derivative to real part 17/16,
then combine its numerical bound with Gamma's compact and quartic bounds.
This integrable envelope retains the conductor logarithm explicitly. -/
theorem gamma_left_integrand_bound {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      (20000 * (Real.log q + 1) * x ^ (-9 / 16 : ℝ)) * (1 + t ^ 2)⁻¹ := by
  let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  have hs : (s + 1 / 2).re = (-1 / 16 : ℝ) := by
    norm_num only [s, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero]
  have hi : (s + 1 / 2).im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.div_ofNat_im, Complex.one_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, one_mul, zero_mul, zero_div,
      zero_add, add_zero]
  have he : s + 1 / 2 = ((-1 / 16 : ℝ) : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  have hg32 := Analysis.norm_Gamma_neg_one_sixteenth_le_thirty_two hs
  have hg4 : ‖Complex.Gamma (s + 1 / 2)‖ * |t| ^ 4 ≤ 6 := by
    by_cases ht : t = 0
    · rw [ht]
      norm_num only [mul_zero]
    · have hi0 : (s + 1 / 2).im ≠ 0 := by
        rw [hi]; exact ht
      have h := Analysis.norm_Gamma_neg_one_sixteenth_le_fourth hs hi0
      rw [hi] at h
      have ht4 : 0 < t ^ 4 := by nlinarith only [sq_pos_of_ne_zero ht]
      have hm := (le_div_iff₀ ht4).mp h
      have habs4 : |t| ^ 4 = t ^ 4 := by nlinarith only [sq_abs t]
      rw [habs4]
      exact hm
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hnlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have hd :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_neg_one_sixteenth_le hp hne hinv
      t
  rw [hnlog, ← he] at hd
  have hm :=
    gamma_left_envelope hlog (abs_nonneg t) (norm_nonneg (Complex.Gamma (s + 1 / 2))) hg32 hg4
  rw [sq_abs] at hm
  have hdg := mul_le_mul_of_nonneg_right hd (norm_nonneg (Complex.Gamma (s + 1 / 2)))
  have hden : 0 < 1 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hb :
    ‖logDeriv χ.completedLFunction (s + 1 / 2)‖ * ‖Complex.Gamma (s + 1 / 2)‖ ≤
      (20000 * (Real.log q + 1)) / (1 + t ^ 2) := by
    apply (le_div_iff₀ hden).mpr
    have hmul := mul_le_mul_of_nonneg_right hdg hden.le
    nlinarith only [hm, hmul]
  change
    ‖-logDeriv χ.completedLFunction (s + 1 / 2) * (Complex.Gamma (s + 1 / 2) * (x : ℂ) ^ s)‖ ≤ _
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hsr : s.re = (-9 / 16 : ℝ) := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hsr, ← mul_assoc]
  have hmul := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx.le (-9 / 16))
  exact hmul.trans_eq (by ring)

/-- The normalized left completed integral at a=-9/16 has norm at most
10000(log(q)+1)x^a for positive scale and primitive nonprincipal data with
nonprincipal inverse. Integrate the rational envelope and divide by 2π.
All constants are numerical and no RH hypothesis is needed for this integral bound. -/
theorem norm_gamma_left_integral_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      10000 * (Real.log q + 1) * x ^ (-9 / 16 : ℝ) := by
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
        (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hfi : MeasureTheory.Integrable F :=
    MellinKernel.integrable_completed_left_line gammaMellinKernel hp hne hinv
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  let E := 20000 * (Real.log q + 1) * x ^ (-9 / 16 : ℝ)
  have hgi := integrable_inv_one_add_sq.const_mul E
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gamma_left_integrand_bound hp hne hinv hx t))
  rw [MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq] at hb
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (E * Real.pi) :=
      mul_le_mul_of_nonneg_left hb
        (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))
    _ = _ := by
      dsimp only [E]
      field_simp (discharger :=
        first
        | (norm_num only; done)
        | exact Real.pi_pos.ne')
      ring

/-- At scale x≥1, the fixed Gamma left completed integral is bounded by
10000(log(q)+1)/sqrt(x). Compare the line's real-power factor x^(-9/16)
with x^(-1/2). This is the explicit left error in the primitive Mellin formula. -/
theorem norm_gamma_left_integral_le_div_sqrt {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      10000 * (Real.log q + 1) / Real.sqrt x := by
  have hpw := Real.rpow_le_rpow_of_exponent_le hx (by norm_num only : (-9 / 16 : ℝ) ≤ -1 / 2)
  have he : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [neg_div, Real.rpow_neg (zero_le_one.trans hx), ← Real.sqrt_eq_rpow, one_div]
  rw [he] at hpw
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hc : 0 ≤ 10000 * (Real.log q + 1) := by nlinarith only [Real.log_nonneg hq1]
  exact
    (norm_gamma_left_integral_le hp hne hinv (zero_lt_one.trans_le hx)).trans
      ((mul_le_mul_of_nonneg_left hpw hc).trans_eq (by ring))

end PseudoPrime.LLS.PaperStatements
