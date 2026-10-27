/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapUntwistedBounds
public import PseudoPrime.LLS.QuadraticDigammaIntegralExchange
public import PseudoPrime.LLS.TriangularGammaIntegralSeries

/-! # Signed Gamma-series decomposition for adjustable reciprocal kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The actual adjustable rational kernel on the imaginary axis multiplied by the Mellin
phase x^(it). Positive x gives phase norm one. This weight keeps the exact integrands
visible during the signed Gamma-series exchange. -/
noncomputable def reciprocalGapCentralWeight (h x t : ℝ) : ℂ :=
  Analysis.reciprocalGapFunction h (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)

/-- For positive gap and scale, the actual central weight is continuous.
Both shifted denominators have positive real parts and the Mellin phase is continuous.
This verifies the regularity premise of the quadratic-decay exchange theorem. -/
theorem continuous_reciprocalGapCentralWeight {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    Continuous (reciprocalGapCentralWeight h x) := by
  have hn (a : ℝ) (ha : 0 < a) (t : ℝ) : Complex.I * (t : ℂ) + (a : ℂ) ≠ 0 := by
    have hr : 0 < (Complex.I * (t : ℂ) + (a : ℂ)).re := by
      simpa only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, zero_add] using ha
    exact ne_of_apply_ne Complex.re (by simpa only [Complex.zero_re] using hr.ne')
  have hK : Continuous (fun t : ℝ ↦ Analysis.reciprocalGapFunction h (Complex.I * t)) :=
    continuous_const.div
      (((continuous_const.mul Complex.continuous_ofReal).add continuous_const).mul
        ((continuous_const.mul Complex.continuous_ofReal).add continuous_const))
      (fun t ↦
        mul_ne_zero (hn (1 / 2) (by norm_num only) t) (hn (1 / 2 + h) (by linarith only [hh]) t))
  have hP : Continuous (fun t : ℝ ↦ (x : ℂ) ^ (Complex.I * t)) :=
    (continuous_const.mul Complex.continuous_ofReal).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  exact hK.mul hP

/-- For nonnegative gap and positive scale, the actual central weight is bounded by
4/(1+t^2). The phase has unit norm and the rational kernel has a common majorant.
This gives decay uniformly in the gap without an absolute first moment assumption. -/
theorem norm_reciprocalGapCentralWeight_le {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (t : ℝ) :
    ‖reciprocalGapCentralWeight h x t‖ ≤ 4 / (1 + t ^ 2) := by
  rw [reciprocalGapCentralWeight, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
    sub_zero, Real.rpow_zero, mul_one]
  exact reciprocalGap_central_norm_le hh t

/-- For positive gap, digamma base and scale, integrate the actual weighted digamma
difference term by term. Use the general quadratic-decay exchange theorem.
The resulting series retains the signs of the reciprocal differences. -/
theorem reciprocalGap_digamma_vertical_sub_integral_eq_tsum {h b x : ℝ} (hh : 0 < h) (hb : 0 < b)
    (hx : 0 < x) :
    (∫ t : ℝ,
        (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
          reciprocalGapCentralWeight h x t) =
      ∑' n : ℕ,
        ∫ t : ℝ,
          (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
            reciprocalGapCentralWeight h x t := by
  exact
    integral_quadratic_weight_digamma_vertical_sub_eq_tsum hb (reciprocalGapCentralWeight h x)
      (continuous_reciprocalGapCentralWeight hh hx) (norm_reciprocalGapCentralWeight_le hh.le hx)

/-- For positive gap and scale, the normalized central weight integral equals the compact
two-pole Mellin profile at the inverse scale. Specialize the proved inverse transform.
This evaluates the baseline term in the signed Gamma decomposition. -/
theorem reciprocalGap_central_weight_integral_eq_profile {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, reciprocalGapCentralWeight h x t) =
      AnalyticNumberTheory.General.twoPoleMellinWeight (1 / 2) h x⁻¹ := by
  have hm := inverseMellin_reciprocalGap hh (c := 0) (u := x⁻¹) (by norm_num only) (inv_pos.mpr hx)
  unfold inverseMellin at hm
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at hm
  exact hm

/-- For positive gap and scale, the actual central weight is integrable.
Rewrite the phase as the inverse-Mellin power on the central line.
This permits splitting the baseline from the digamma difference. -/
theorem integrable_reciprocalGapCentralWeight {h x : ℝ} (hh : 0 < h) (hx : 0 < x) :
    MeasureTheory.Integrable (reciprocalGapCentralWeight h x) := by
  have hi :=
    integrable_inverseMellin_reciprocalGap hh (c := 0) (u := x⁻¹) (by norm_num only)
      (inv_pos.mpr hx)
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at hi
  exact hi

/-- For every character, a parity base b in [1/4,1] expresses the central Gamma integral
for all positive gaps and scales as its explicit compact-profile baseline plus the
convergent series of weighted reciprocal-difference integrals.
Split the integrable digamma baseline and use the quadratic-decay exchange theorem.
This exact identity preserves signs; scalar resolvent inversion is still required. -/
theorem reciprocalGap_central_gammaIntegral_eq_resolvent_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ {h x : ℝ},
          0 < h →
            0 < x →
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∫ t : ℝ,
                  logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                    reciprocalGapCentralWeight h x t) =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
                  AnalyticNumberTheory.General.twoPoleMellinWeight (1 / 2) h x⁻¹ +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) / 2) *
                  (∑' n : ℕ,
                    ∫ t : ℝ,
                      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                        reciprocalGapCentralWeight h x t) := by
  obtain ⟨b, hb, hb1, hp⟩ := gamma_central_eq_complex_digamma χ
  refine ⟨b, hb, hb1, ?_⟩
  intro h x hh hx
  let K := reciprocalGapMellinKernel h hh
  let W := reciprocalGapCentralWeight h x
  let B := (-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2
  let D := fun t : ℝ ↦
    (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t
  have hW : MeasureTheory.Integrable W := integrable_reciprocalGapCentralWeight hh hx
  have hG0 :=
    MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := x) (by norm_num only)
      (by linarith only [K.delta_pos]) (by norm_num only) hx
  have hG :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t) := by
    simpa only [K, reciprocalGapMellinKernel, W, reciprocalGapCentralWeight, Complex.ofReal_zero,
      zero_add, mul_assoc] using hG0
  have he (t : ℝ) :
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t = B * W t + (1 / 2 : ℂ) * D t := by
    rw [hp]
    dsimp only [B, D]
    ring
  have hD : MeasureTheory.Integrable D :=
    ((hG.sub (hW.const_mul B)).const_mul (2 : ℂ)).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change 2 * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t - B * W t) = D t
          rw [he]
          ring))
  have hseries :=
    reciprocalGap_digamma_vertical_sub_integral_eq_tsum hh
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hx
  change (∫ t : ℝ, D t) = _ at hseries
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add (hW.const_mul B) (hD.const_mul (1 / 2 : ℂ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hseries]
  have hm := reciprocalGap_central_weight_integral_eq_profile hh hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = _ at hm
  rw [← hm]
  dsimp only [B]
  ring

/-- For positive gap and scale at least one, subtracting the first-pole residue and left
integral from the completed remainder leaves the exact central Gamma integral.
Use the contour decomposition and the proved right-to-central line shift.
This connects the signed Gamma series to the actual witness remainder without a norm bound. -/
theorem reciprocalGap_remainder_sub_pole_left_eq_central_gamma {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 1 ≤ x) :
    reciprocalGapCompletedRemainder h hh χ x -
        MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
        reciprocalGapLeftIntegral h hh χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * reciprocalGapCentralWeight h x t) := by
  let K := reciprocalGapMellinKernel h hh
  let b := 1 / 2 + K.delta / 2
  have hd := K.delta_pos
  have hu : K.delta ≤ (1 / 8 : ℝ) := min_le_right _ _
  have he :=
    MellinKernel.gammaIntegral_eq_central K χ (b := b)
      (by
        dsimp only [b]; linarith only [hd])
      (by
        dsimp only [b]; linarith only [hd])
      (by
        dsimp only [b]; linarith only [hu])
      hx
  have hr :
    reciprocalGapCompletedRemainder h hh χ x -
        MellinKernel.weightedResidue K (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
        reciprocalGapLeftIntegral h hh χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((b : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) := by
    dsimp only [reciprocalGapCompletedRemainder, reciprocalGapLeftIntegral, K, b]
    ring
  rw [hr, he]
  rfl

end PseudoPrime.LLS.PaperStatements
