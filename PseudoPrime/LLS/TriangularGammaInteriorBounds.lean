/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularGammaPositiveScale
public import PseudoPrime.LLS.TriangularSignedGammaBounds
public import PseudoPrime.AnalyticNumberTheory.General.TriangularGammaInteriorBounds

/-!
# Signed Gamma bounds inside the triangular logarithmic support

Evaluate the real-pole resolvents explicitly. At both scales the reciprocal correction
is bounded above by half an inverse square, while the negative Gamma baseline remains.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive pole coordinate and 0≤l≤2a, the reciprocal difference at exp(-l)
is (1-exp(-2c(2a-l)))/(2c²). Evaluate the three shifted resolvents and cancel the
linear profile term. This is the inverse-scale interior Gamma correction. -/
theorem triangularGammaReciprocalTerm_exp_neg {a c l : ℝ} (hc : 0 < c) (hl : 0 ≤ l)
    (hla : l ≤ 2 * a) :
    triangularGammaReciprocalTerm a c (Real.exp (-l)) =
      (((1 - Real.exp (-2 * c * (2 * a - l))) / (2 * c ^ 2) : ℝ) : ℂ) := by
  have ha : 0 ≤ a := by linarith only [hl, hla]
  have he1 : l - 2 * a = -(2 * a - l) := by ring
  have hp : triangularKernelProfile a (Real.exp (-l)) = 2 * a - l := by
    unfold triangularKernelProfile
    rw [Real.log_exp, abs_neg, abs_of_nonneg hl, max_eq_right (sub_nonneg.mpr hla)]
  unfold triangularGammaReciprocalTerm
  rw [hp, ← Real.exp_neg, neg_neg, ← Real.exp_sub, ← Real.exp_sub, he1,
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_neg (sub_nonneg.mpr hla),
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_nonneg
      (by linarith only [ha, hl] : 0 ≤ l - -2 * a),
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_nonneg hl]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat, add_zero, mul_zero, sub_zero]
  have hn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hd : (2 : ℂ) * (c : ℂ) ^ 2 ≠ 0 := mul_ne_zero (by norm_num only) (pow_ne_zero 2 hn)
  apply (eq_div_iff hd).mpr
  rw [sub_mul]
  have hfirst :
    (((2 * a - l : ℝ) : ℂ) / c) * (2 * (c : ℂ) ^ 2) = 2 * c * ((2 * a - l : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    calc
      _ = (2 * c * ((2 * a - l : ℝ) : ℂ)) * ((c : ℂ) * (c : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one]
  have hsecond (z : ℂ) : (2 * (z / (4 * (c : ℂ) ^ 2))) * (2 * (c : ℂ) ^ 2) = z := by
    calc
      _ = z * ((4 * (c : ℂ) ^ 2) / (4 * (c : ℂ) ^ 2)) := by ring
      _ = _ := by rw [div_self (mul_ne_zero (by norm_num only) (pow_ne_zero 2 hn)), mul_one]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] at hfirst
  rw [hfirst, hsecond]
  ring

/-- For positive pole coordinate and 0≤l≤2a, the reciprocal difference at exp(l)
is (-1+2exp(-2cl)-exp(-2c(l+2a)))/(2c²). Evaluate the shifted resolvents and cancel
the linear terms. This retains the signed correction at the direct scale. -/
theorem triangularGammaReciprocalTerm_exp_pos {a c l : ℝ} (hc : 0 < c) (hl : 0 ≤ l)
    (hla : l ≤ 2 * a) :
    triangularGammaReciprocalTerm a c (Real.exp l) =
      (((-1 + 2 * Real.exp (-2 * c * l) - Real.exp (-2 * c * (l + 2 * a))) / (2 * c ^ 2) : ℝ) :
        ℂ) := by
  have ha : 0 ≤ a := by linarith only [hl, hla]
  have he1 : -l - 2 * a = -(l + 2 * a) := by ring
  have hp : triangularKernelProfile a (Real.exp l) = 2 * a - l := by
    unfold triangularKernelProfile
    rw [Real.log_exp, abs_of_nonneg hl, max_eq_right (sub_nonneg.mpr hla)]
  unfold triangularGammaReciprocalTerm
  rw [hp, ← Real.exp_neg, ← Real.exp_sub, ← Real.exp_sub, he1,
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_neg
      (by linarith only [ha, hl] : 0 ≤ l + 2 * a),
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_nonneg
      (by linarith only [hla] : 0 ≤ -l - -2 * a),
    AnalyticNumberTheory.General.mellinResolventWeight_realPole_exp_neg hl]
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_neg, add_zero]
  have hn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hd : (2 : ℂ) * (c : ℂ) ^ 2 ≠ 0 := mul_ne_zero (by norm_num only) (pow_ne_zero 2 hn)
  apply (eq_div_iff hd).mpr
  rw [sub_mul]
  have hfirst :
    (((2 * a - l : ℝ) : ℂ) / c) * (2 * (c : ℂ) ^ 2) = 2 * c * ((2 * a - l : ℝ) : ℂ) := by
    rw [div_eq_mul_inv]
    calc
      _ = (2 * c * ((2 * a - l : ℝ) : ℂ)) * ((c : ℂ) * (c : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hn, mul_one]
  have hsecond (z : ℂ) : (2 * (z / (4 * (c : ℂ) ^ 2))) * (2 * (c : ℂ) ^ 2) = z := by
    calc
      _ = z * ((4 * (c : ℂ) ^ 2) / (4 * (c : ℂ) ^ 2)) := by ring
      _ = _ := by rw [div_self (mul_ne_zero (by norm_num only) (pow_ne_zero 2 hn)), mul_one]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat] at hfirst
  rw [mul_sub, sub_mul, hfirst, hsecond]
  have hlast (z : ℂ) : (2 * (2 * (z / (4 * (c : ℂ) ^ 2)))) * (2 * (c : ℂ) ^ 2) = 2 * z := by
    calc
      _ = 2 * ((2 * (z / (4 * (c : ℂ) ^ 2))) * (2 * (c : ℂ) ^ 2)) := by ring
      _ = _ := by rw [hsecond]
  rw [hlast]
  ring

/-- For positive c and 0≤l≤2a, the inverse-scale reciprocal term has real part
at most half the inverse square of c. Use its elementary exponential formula and
positivity of the exponential. This supplies the summable Gamma correction budget. -/
theorem triangularGammaReciprocalTerm_exp_neg_re_le {a c l : ℝ} (hc : 0 < c) (hl : 0 ≤ l)
    (hla : l ≤ 2 * a) :
    (triangularGammaReciprocalTerm a c (Real.exp (-l))).re ≤ (1 / 2) * (c ^ 2)⁻¹ := by
  rw [triangularGammaReciprocalTerm_exp_neg hc hl hla, Complex.ofReal_re]
  have hd : 0 < 2 * c ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hc)
  calc
    _ ≤ 1 / (2 * c ^ 2) := div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) hd.le
    _ = _ := by ring

/-- For positive c and 0≤l≤2a, the direct-scale reciprocal term has real part
at most half the inverse square of c. Its first exponential is at most one and the
last is positive. This gives the same budget at both scales. -/
theorem triangularGammaReciprocalTerm_exp_pos_re_le {a c l : ℝ} (hc : 0 < c) (hl : 0 ≤ l)
    (hla : l ≤ 2 * a) :
    (triangularGammaReciprocalTerm a c (Real.exp l)).re ≤ (1 / 2) * (c ^ 2)⁻¹ := by
  rw [triangularGammaReciprocalTerm_exp_pos hc hl hla, Complex.ofReal_re]
  have hd : 0 < 2 * c ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hc)
  have he : Real.exp (-2 * c * l) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hc, hl])
  have hn : -1 + 2 * Real.exp (-2 * c * l) - Real.exp (-2 * c * (l + 2 * a)) ≤ 1 := by
    linarith only [he, (Real.exp_pos (-2 * c * (l + 2 * a)))]
  calc
    _ ≤ 1 / (2 * c ^ 2) := div_le_div_of_nonneg_right hn hd.le
    _ = _ := by ring

/-- For positive a, parity base b≥1/4, 0≤l≤2a and either sign, the real part of
the reciprocal series at exp(±l) is at most nine. Move the real part through the
convergent series and sum the inverse-square majorant. This bounds the Gamma correction. -/
theorem triangularGammaReciprocalSeries_exp_re_le_nine {a b l : ℝ} (ha : 0 < a) (hb : 1 / 4 ≤ b)
    (hl : 0 ≤ l) (hla : l ≤ 2 * a) (e : ℝ) (he : e = 1 ∨ e = -1) :
    (∑' n : ℕ, triangularGammaReciprocalTerm a (b + n) (Real.exp (e * l))).re ≤ 9 := by
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num only) hb
  have hs := summable_triangularGammaReciprocalTerm ha hb0 (Real.exp_pos (e * l))
  have hsre :
    Summable (fun n : ℕ ↦ (triangularGammaReciprocalTerm a (b + n) (Real.exp (e * l))).re) :=
    hs.map Complex.reCLM Complex.reCLM.continuous
  have hm := (Analysis.summable_shifted_inverse_squares hb0).mul_left (1 / 2 : ℝ)
  have ht (n : ℕ) :
    (triangularGammaReciprocalTerm a (b + n) (Real.exp (e * l))).re ≤
      (1 / 2) * ((b + n) ^ 2)⁻¹ := by
    have hc := add_pos_of_pos_of_nonneg hb0 (Nat.cast_nonneg n)
    rcases he with rfl | rfl
    · simpa only [one_mul] using triangularGammaReciprocalTerm_exp_pos_re_le (a := a) hc hl hla
    · simpa only [neg_one_mul] using triangularGammaReciprocalTerm_exp_neg_re_le (a := a) hc hl hla
  have hsum := Summable.tsum_le_tsum ht hsre hm
  rw [tsum_mul_left] at hsum
  rw [Complex.re_tsum hs]
  have hbnd := Analysis.shifted_inverse_square_sum_le_eighteen hb
  linarith only [hsum, hbnd]

/-- For every character, positive a, 0≤l≤2a and either sign, the normalized central
Gamma integral has real part at most -3(2a-l)/4+9/2. Retain the negative baseline
and use the summed reciprocal bound. This evaluates the interior signed Gamma cost. -/
theorem triangular_central_gamma_exp_re_le_profile {q : ℕ} (χ : DirichletCharacter ℂ q) {a l : ℝ}
    (ha : 0 < a) (hl : 0 ≤ l) (hla : l ≤ 2 * a) (e : ℝ) (he : e = 1 ∨ e = -1) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              (Analysis.triangularMellinFunction a (Complex.I * t) *
                (Real.exp (e * l) : ℂ) ^ (Complex.I * t)))).re ≤
      -(3 / 4) * (2 * a - l) + 9 / 2 := by
  obtain ⟨b, hb, hb1, hg⟩ := triangular_central_gammaIntegral_eq_weight_series χ
  have hp : triangularKernelProfile a (Real.exp (e * l)) = 2 * a - l := by
    unfold triangularKernelProfile
    rcases he with rfl | rfl
    · rw [one_mul, Real.log_exp, abs_of_nonneg hl, max_eq_right (sub_nonneg.mpr hla)]
    · rw [neg_one_mul, Real.log_exp, abs_neg, abs_of_nonneg hl, max_eq_right (sub_nonneg.mpr hla)]
  have hbase := gamma_real_baseline_le_neg_three_quarters (lt_of_lt_of_le (by norm_num only) hb) hb1
  have hseries := triangularGammaReciprocalSeries_exp_re_le_nine ha hb hl hla e he
  rw [hg a (Real.exp (e * l)) ha (Real.exp_pos _), hp, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, complex_div_two_re]
  norm_num only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.log_ofReal_re,
    Complex.mul_re, Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im, Complex.one_im,
    zero_div, zero_mul, sub_zero]
  have hscaled := mul_le_mul_of_nonneg_right hbase (sub_nonneg.mpr hla)
  linarith only [hscaled, hseries]

/-- For every character, 1≤x with log x≤36 and a line between zero and five eighths,
the normalized alpha-18 Gamma integral has real part at most -3(36-log x)/4+9/2.
Shift to the center and use the signed interior series bound. No GRH is required. -/
theorem triangular18_gammaIntegral_re_le_interior {q : ℕ} (χ : DirichletCharacter ℂ q) {b x : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 1 ≤ x) (hlog : Real.log x ≤ 36) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))).re ≤
      -(3 / 4) * (36 - Real.log x) + 9 / 2 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hxpos := zero_lt_one.trans_le hx
  have he :=
    MellinKernel.gammaIntegral_eq_central_of_pos K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) hxpos
  have h :=
    triangular_central_gamma_exp_re_le_profile χ (a := 18) (by norm_num only) (Real.log_nonneg hx)
      (by
        norm_num only at hlog ⊢; exact hlog)
      1 (Or.inl rfl)
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * _).re ≤ _
  rw [he]
  simpa only [K, triangularMellinKernel, one_mul, Real.exp_log hxpos,
    show (2 : ℝ) * 18 = 36 by norm_num only] using h

/-- For every character, 1≤x with log x≤36 and an admissible right line, the
inverse-scale alpha-18 Gamma integral has real part at most -3(36-log x)/4+9/2.
The positive-scale contour shift and negative logarithmic coordinate give this bound. -/
theorem triangular18_inverse_gammaIntegral_re_le_interior {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 1 ≤ x) (hlog : Real.log x ≤ 36) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function ((b : ℂ) + Complex.I * t) * (x⁻¹ : ℂ) ^ ((b : ℂ) + Complex.I * t)))).re ≤
      -(3 / 4) * (36 - Real.log x) + 9 / 2 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hxpos := zero_lt_one.trans_le hx
  have he :=
    MellinKernel.gammaIntegral_eq_central_of_pos K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) (inv_pos.mpr hxpos)
  have h :=
    triangular_central_gamma_exp_re_le_profile χ (a := 18) (by norm_num only) (Real.log_nonneg hx)
      (by
        norm_num only at hlog ⊢; exact hlog)
      (-1) (Or.inr rfl)
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * _).re ≤ _
  simp only [Complex.ofReal_inv] at he
  rw [he]
  simpa only [K, triangularMellinKernel, neg_one_mul, Real.exp_neg, Real.exp_log hxpos,
    Complex.ofReal_inv, show (2 : ℝ) * 18 = 36 by norm_num only] using h

end PseudoPrime.LLS.PaperStatements
