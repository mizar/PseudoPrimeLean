/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapSignedGammaBounds
public import PseudoPrime.AnalyticNumberTheory.General.TwoPoleMiddleMellin

/-! # Signed conductor decomposition of adjustable reciprocal left integrals -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive gap, positive input and a line strictly between the two poles, the
project inverse Mellin integral equals the negative middle-strip profile.
Translate the general Mellin inversion convention. This evaluates the actual left contour. -/
theorem inverseMellin_reciprocalGap_middle {h c u : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hu : 0 < u) :
    inverseMellin (Analysis.reciprocalGapFunction h) c u =
      AnalyticNumberTheory.General.twoPoleMiddleWeight (1 / 2) h u := by
  change inverseMellin (Analysis.twoPoleFunction (1 / 2) (1 / 2 + h)) c u = _
  rw [←
    AnalyticNumberTheory.General.mellinInv_twoPoleMiddleWeight hh
      (show c + 1 / 2 < 0 by linarith only [hcu]) (show 0 < c + 1 / 2 + h by linarith only [hcl])
      hu]
  unfold inverseMellin mellinInv
  rw [Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul, mul_comm]

/-- At scale x>=1, the normalized kernel integral on any line between its poles is
-x^(-1/2-h)/h. Invert at 1/x and evaluate the small-argument middle-profile branch.
This exact negative value replaces the conductor term's absolute norm estimate. -/
theorem reciprocalGap_left_kernel_integral {h c x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) =
      ((-x ^ (-1 / 2 - h) / h : ℝ) : ℂ) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hi : x⁻¹ ≤ 1 := by
    have hdiv : (1 : ℝ) / x ≤ 1 := (div_le_one hx0).mpr hx
    simpa only [one_div] using hdiv
  have hm := inverseMellin_reciprocalGap_middle hh hcl hcu (inv_pos.mpr hx0)
  unfold inverseMellin at hm
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx0.le,
    inv_inv] at hm
  rw [AnalyticNumberTheory.General.twoPoleMiddleWeight_small hh (inv_pos.mpr hx0) hi,
    Real.inv_rpow hx0.le, ← Real.rpow_neg hx0.le] at hm
  have he : -(1 / 2 + h : ℝ) = -1 / 2 - h := by ring
  rw [he] at hm
  exact hm

/-- On a line strictly between the rational poles and at positive scale, the kernel times
the Mellin power is integrable. Use general vertical integrability on any nonpole line
and the constant norm of the power. Positivity of h follows from the line conditions. -/
theorem integrable_reciprocalGap_middle_kernel {h c x : ℝ} (hcl : -1 / 2 - h < c) (hcu : c < -1 / 2)
    (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
          (x : ℂ) ^ ((c : ℂ) + Complex.I * t)) := by
  have hf :=
    AnalyticNumberTheory.General.verticalIntegrable_twoPoleFunction_of_ne (a := 1 / 2) (b :=
      1 / 2 + h) (σ := c) (by linarith only [hcu]) (by linarith only [hcl])
  unfold Complex.VerticalIntegrable at hf
  have hline :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t)) :=
    hf.congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          unfold Analysis.reciprocalGapFunction
          change
            Analysis.twoPoleFunction (1 / 2) (1 / 2 + h) ((c : ℂ) + (t : ℂ) * Complex.I) =
              Analysis.twoPoleFunction (1 / 2) (1 / 2 + h) ((c : ℂ) + Complex.I * t)
          rw [mul_comm (t : ℂ) Complex.I]))
  have hi := integrable_inverseMellin_of_line (inv_pos.mpr hx) hline
  simpa only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] using hi

/-- For primitive nonprincipal data with nonprincipal inverse and Re(s)<-1/2, the negative
completed logarithmic derivative at s+1/2 equals log(q) plus the inverse character's
completed logarithmic derivative at 1/2-s. Apply the functional equation and right nonvanishing.
This preserves the conductor sign before integrating the left contour. -/
theorem reciprocalGap_completed_reflection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {s : ℂ} (hs : s.re < -1 / 2) :
    -logDeriv χ.completedLFunction (s + 1 / 2) =
      Complex.log q + logDeriv χ⁻¹.completedLFunction (1 / 2 - s) := by
  have hr : 1 ≤ (1 / 2 - s).re := by
    rw [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
    linarith only [hs]
  have he :=
    AnalyticNumberTheory.DirichletLFunction.completedLFunction_logDeriv_functionalEquation_at hp hne
      (s := 1 / 2 - s)
      (AnalyticNumberTheory.DirichletLFunction.completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hz : (1 : ℂ) - (1 / 2 - s) = s + 1 / 2 := by ring
  rw [hz] at he
  exact he

/-- At scale x>=1 and any line between the poles, the conductor-weighted kernel integral
is exactly -log(q)*x^(-1/2-h)/h for natural q. Extract the constant and use middle-strip inversion.
This is a signed identity, with no GRH or character assumptions. -/
theorem reciprocalGap_conductor_kernel_integral {h c x : ℝ} (hh : 0 < h) (hcl : -1 / 2 - h < c)
    (hcu : c < -1 / 2) (hx : 1 ≤ x) (q : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.log q *
            (Analysis.reciprocalGapFunction h ((c : ℂ) + Complex.I * t) *
              (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) =
      ((-Real.log q * x ^ (-1 / 2 - h) / h : ℝ) : ℂ) := by
  rw [MeasureTheory.integral_const_mul, mul_left_comm,
    reciprocalGap_left_kernel_integral hh hcl hcu hx, ← Complex.natCast_log]
  simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The normalized integral of the inverse character's completed logarithmic derivative
at 1/2-s against K_h(s)*x^s on the actual left line -1/2-delta(h)/2.
It isolates the reflected contribution after evaluating the conductor integral exactly. -/
noncomputable def reciprocalGapReflectedIntegral {q : ℕ} [NeZero q] (h : ℝ) (hh : 0 < h)
    (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  let K := reciprocalGapMellinKernel h hh
  let a := -1 / 2 - K.delta / 2
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ⁻¹.completedLFunction (1 / 2 - ((a : ℂ) + Complex.I * t)) *
        (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)))

/-- For primitive nonprincipal data with nonprincipal inverse, the actual reflected
completed integrand is integrable at positive scale. Subtract the integrable conductor
kernel from the original left completed integrand using the exact functional equation.
This justifies the signed integral split without an extra convergence assumption. -/
theorem integrable_reciprocalGap_reflected_line {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    let K := reciprocalGapMellinKernel h hh
    let a := -1 / 2 - K.delta / 2
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ⁻¹.completedLFunction (1 / 2 - ((a : ℂ) + Complex.I * t)) *
          (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))) := by
  let K := reciprocalGapMellinKernel h hh
  let a := -1 / 2 - K.delta / 2
  have hd := K.delta_pos
  have hu : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
  have hhδ : K.delta ≤ h / 4 := min_le_left _ _
  have hal : a < -1 / 2 := by
    dsimp only [a]; linarith only [hd]
  have hW :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)) := by
    simpa only [K, reciprocalGapMellinKernel] using
      integrable_reciprocalGap_middle_kernel
        (show -1 / 2 - h < a by
          dsimp only [a]; linarith only [hhδ, hh])
        hal hx
  have hF :=
    MellinKernel.integrable_completed_left_line K hp hne hinv
      (by
        dsimp only [a]; linarith only [hd])
      hal
      (by
        dsimp only [a]; linarith only [hu])
      hx
  exact
    (hF.sub (hW.const_mul (Complex.log q))).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          have hs : ((a : ℂ) + Complex.I * (t : ℂ)).re < -1 / 2 := by
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hal
          simp only [Pi.sub_apply]
          rw [reciprocalGap_completed_reflection hp hne hinv hs]
          change
            (Complex.log q + logDeriv χ⁻¹.completedLFunction (1 / 2 - ((a : ℂ) + Complex.I * t))) *
                  (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)) -
                Complex.log q *
                  (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)) =
              logDeriv χ⁻¹.completedLFunction (1 / 2 - ((a : ℂ) + Complex.I * t)) *
                (K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t))
          ring))

/-- For positive gap, scale at least one and primitive nonprincipal data with nonprincipal
inverse, the actual left integral equals -log(q)*x^(-1/2-h)/h plus the reflected integral.
Split integrable terms under the functional equation and evaluate the conductor kernel.
No GRH is needed; the negative conductor contribution is retained. -/
theorem reciprocalGap_leftIntegral_eq_conductor_add_reflected {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    reciprocalGapLeftIntegral h hh χ x =
      ((-Real.log q * x ^ (-1 / 2 - h) / h : ℝ) : ℂ) + reciprocalGapReflectedIntegral h hh χ x := by
  let K := reciprocalGapMellinKernel h hh
  let a := -1 / 2 - K.delta / 2
  let W := fun t : ℝ ↦ K.function ((a : ℂ) + Complex.I * t) * (x : ℂ) ^ ((a : ℂ) + Complex.I * t)
  have hd := K.delta_pos
  have hhδ : K.delta ≤ h / 4 := min_le_left _ _
  have hal : a < -1 / 2 := by
    dsimp only [a]; linarith only [hd]
  have hlow : -1 / 2 - h < a := by
    dsimp only [a]; linarith only [hhδ, hh]
  have hW : MeasureTheory.Integrable W :=
    integrable_reciprocalGap_middle_kernel hlow hal (zero_lt_one.trans_le hx)
  have hR := integrable_reciprocalGap_reflected_line hh hp hne hinv (zero_lt_one.trans_le hx)
  have he (t : ℝ) :
    -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) * W t =
      Complex.log q * W t +
        logDeriv χ⁻¹.completedLFunction (1 / 2 - ((a : ℂ) + Complex.I * t)) * W t := by
    have hs : ((a : ℂ) + Complex.I * (t : ℂ)).re < -1 / 2 := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hal
    rw [reciprocalGap_completed_reflection hp hne hinv hs]
    ring
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add (hW.const_mul (Complex.log q)) hR, mul_add]
  have hC := reciprocalGap_conductor_kernel_integral hh hlow hal hx q
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, Complex.log q * W t) = _ at hC
  rw [hC]
  rfl

end PseudoPrime.LLS.PaperStatements
