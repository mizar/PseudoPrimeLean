/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularGammaIntegralSeries
public import PseudoPrime.AnalyticNumberTheory.General.TriangularResolventContour

/-! # Explicit weight series for the central triangular Gamma integral -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive triangular parameter and scale, the normalized central kernel
integral is the real triangular profile. Invert at inverse scale and use the even
absolute logarithm. This evaluates the constant part of each reciprocal difference. -/
theorem triangular_central_kernelIntegral_eq_profile {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Analysis.triangularMellinFunction a (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) =
      (triangularKernelProfile a x : ℂ) := by
  have h :=
    inverseMellin_triangular ha (c := 0) (u := x⁻¹) (by norm_num only [abs_zero]) (inv_pos.mpr hx)
  unfold inverseMellin at h
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at h
  unfold triangularKernelProfile at h ⊢
  rw [Real.log_inv, abs_neg] at h
  exact h

/-- For positive parameter and scale, the central kernel times its Mellin phase
is integrable. Specialize inverse-strip integrability at inverse scale.
This permits subtracting the constant part of each reciprocal difference. -/
theorem integrable_triangular_central_kernel_power {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        Analysis.triangularMellinFunction a (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) := by
  let K := triangularMellinKernel ha
  have h :=
    MellinKernel.integrable_inverse_in_strip K (c := 0) (u := x⁻¹)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
      (by
        change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (inv_pos.mpr hx)
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at h
  exact h

/-- For positive c and real height, the reciprocal at half height equals twice
the resolvent with pole minus two c. Both denominators are nonzero by positive real parts.
This identifies the Gamma-pole kernel for explicit inversion. -/
theorem gamma_half_reciprocal_eq_resolvent {c : ℝ} (hc : 0 < c) (t : ℝ) :
    1 / ((c : ℂ) + Complex.I * (t / 2)) = 2 / (Complex.I * t - ((-2 * c : ℝ) : ℂ)) := by
  have hn : (c : ℂ) + Complex.I * (t / 2) ≠ 0 := by
    have hr : 0 < ((c : ℂ) + Complex.I * (t / 2)).re := by
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        zero_mul, Complex.div_ofNat_im, Complex.ofReal_im, zero_div, mul_zero, sub_zero,
        add_zero] using hc
    simpa only [Nat.cast_zero, neg_zero] using AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hr 0
  have hd : Complex.I * (t : ℂ) - ((-2 * c : ℝ) : ℂ) ≠ 0 := by
    have hr : 0 < (Complex.I * (t : ℂ) - ((-2 * c : ℝ) : ℂ)).re := by
      simp only [Complex.sub_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      linarith only [hc]
    simpa only [Nat.cast_zero, neg_zero] using AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hr 0
  apply (div_eq_div_iff hn hd).mpr
  simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  ring

/-- For positive parameter, pole coordinate and scale, the normalized reciprocal
difference integral equals its profile divided by c minus twice three translated weights.
Split integrable terms and apply central resolvent inversion. This evaluates each Gamma term. -/
theorem triangular_vertical_reciprocalIntegral_eq_weights {a c x : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
            Analysis.triangularMellinFunction a (Complex.I * t) *
            (x : ℂ) ^ (Complex.I * t)) =
      (triangularKernelProfile a x : ℂ) / c -
        2 *
          (AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
                (x⁻¹ / Real.exp (2 * a)) +
              AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
                (x⁻¹ / Real.exp (-2 * a)) -
            2 * AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ) x⁻¹) := by
  let W := fun t : ℝ ↦
    Analysis.triangularMellinFunction a (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)
  let R := fun t : ℝ ↦
    (Analysis.triangularMellinFunction a (Complex.I * t) / (Complex.I * t - ((-2 * c : ℝ) : ℂ))) *
      (x : ℂ) ^ (Complex.I * t)
  let D := fun t : ℝ ↦
    (1 / (c : ℂ) - 1 / ((c : ℂ) + Complex.I * (t / 2))) *
      Analysis.triangularMellinFunction a (Complex.I * t) *
      (x : ℂ) ^ (Complex.I * t)
  have hW := integrable_triangular_central_kernel_power ha hx
  have hD := integrable_triangular_vertical_resolvent ha hc hx
  have he (t : ℝ) : D t = (1 / (c : ℂ)) * W t - 2 * R t := by
    dsimp only [D, W, R]
    rw [gamma_half_reciprocal_eq_resolvent hc]
    simp only [div_eq_mul_inv]
    ring
  have hR : MeasureTheory.Integrable R :=
    (((hW.const_mul (1 / (c : ℂ))).sub hD).const_mul (1 / 2 : ℂ)).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change 1 / 2 * ((1 / (c : ℂ)) * W t - D t) = R t
          rw [he]
          ring))
  have hα : (((-2 * c : ℝ) : ℂ)).re < 0 := by
    rw [Complex.ofReal_re]
    linarith only [hc]
  have hm :=
    AnalyticNumberTheory.General.mellinInv_triangular_resolvent_central_weight_combination hα ha
      (inv_pos.mpr hx)
  unfold mellinInv at hm
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_zero, zero_add, Complex.ofReal_inv,
    Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at hm
  have hr :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, R t) =
      AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
            (x⁻¹ / Real.exp (2 * a)) +
          AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
            (x⁻¹ / Real.exp (-2 * a)) -
        2 * AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ) x⁻¹ := by
    dsimp only [R]
    simpa only [mul_comm] using hm
  have hk := triangular_central_kernelIntegral_eq_profile ha hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, D t) = _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_sub (hW.const_mul (1 / (c : ℂ))) (hR.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hk, ← hr]
  change
    _ =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t)) / c -
        2 * (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, R t))
  ring

/-- The normalized reciprocal-difference weight for a triangular parameter a,
real pole coordinate c and scale x. It is the profile divided by c minus twice the three
translated regularized resolvent weights at pole minus two c. The definition uses total
real and complex arithmetic; later analytic results assume positive a, c and x.
This supplies the summand of the explicit Gamma integral series. -/
noncomputable def triangularGammaReciprocalTerm (a c x : ℝ) : ℂ :=
  (triangularKernelProfile a x : ℂ) / c -
    2 *
      (AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
            (x⁻¹ / Real.exp (2 * a)) +
          AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ)
            (x⁻¹ / Real.exp (-2 * a)) -
        2 * AnalyticNumberTheory.General.mellinResolventWeight ((-2 * c : ℝ) : ℂ) x⁻¹)

/-- For every character, choose its positive parity base and express the central
triangular Gamma integral at any positive parameter and scale as a baseline profile plus
half the explicit reciprocal-weight series. Replace the integrals term by term with their
proved values. No GRH is required. This removes the unevaluated pole integrals. -/
theorem triangular_central_gammaIntegral_eq_weight_series {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ (a x : ℝ),
          0 < a →
            0 < x →
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∫ t : ℝ,
                  logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                    (Analysis.triangularMellinFunction a (Complex.I * t) *
                      (x : ℂ) ^ (Complex.I * t))) =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
                  (triangularKernelProfile a x : ℂ) +
                (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm a (b + n) x := by
  obtain ⟨b, hb, hb1, hg⟩ := triangular_central_gammaIntegral_eq_vertical_resolvent_series χ
  refine ⟨b, hb, hb1, ?_⟩
  intro a x ha hx
  have he :
    (∑' n : ℕ, triangularGammaReciprocalTerm a (b + n) x) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∑' n : ℕ,
          ∫ t : ℝ,
            (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
              Analysis.triangularMellinFunction a (Complex.I * t) *
              (x : ℂ) ^ (Complex.I * t)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    exact
      (triangular_vertical_reciprocalIntegral_eq_weights ha
          (add_pos_of_pos_of_nonneg (lt_of_lt_of_le (by norm_num only) hb) (Nat.cast_nonneg n))
          hx).symm
  rw [hg a x ha hx, he]
  ring

/-- For positive parameter, parity base and scale, the explicit reciprocal-weight
series is summable. Bound each term's norm by the normalized integral norm and use the
proved integrated absolute convergence. This certifies convergence of the evaluated series. -/
theorem summable_triangularGammaReciprocalTerm {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    Summable (fun n : ℕ ↦ triangularGammaReciprocalTerm a (b + n) x) := by
  have hs := summable_triangular_vertical_resolvent_integral_norm ha hb hx
  apply hs.of_norm_bounded
  intro n
  have he :=
    triangular_vertical_reciprocalIntegral_eq_weights ha
      (add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)) hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = triangularGammaReciprocalTerm a (b + n) x at he
  rw [← he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num only) Real.pi_pos))]
  have h :=
    MeasureTheory.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
      (fun t : ℝ ↦
        (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
          Analysis.triangularMellinFunction a (Complex.I * t) *
          (x : ℂ) ^ (Complex.I * t))
  have hbnd :=
    mul_le_mul_of_nonneg_left h
      (one_div_nonneg.mpr (mul_pos (by norm_num only : (0 : ℝ) < 2) Real.pi_pos).le)
  simpa only [one_div_mul_eq_div] using hbnd

/-- For positive parameter and scale below exp(-2a), the triangular profile is zero.
Compare logarithms and use the maximum definition. This identifies the small-scale branch. -/
theorem triangular_profile_eq_zero_of_small_scale {a x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hsmall : x < Real.exp (-2 * a)) : triangularKernelProfile a x = 0 := by
  have hl := Real.log_lt_log hx hsmall
  rw [Real.log_exp] at hl
  unfold triangularKernelProfile
  rw [abs_of_neg (by linarith only [ha, hl] : Real.log x < 0),
    max_eq_left (by linarith only [hl] : 2 * a - -Real.log x ≤ 0)]

/-- For positive parameter and scale below exp(-2a), every reciprocal-weight term
vanishes, for any real pole coordinate. All translated weights lie outside their support.
This supplies termwise vanishing in the exterior Gamma branch. -/
theorem triangularGammaReciprocalTerm_eq_zero_of_small_scale {a c x : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hsmall : x < Real.exp (-2 * a)) : triangularGammaReciprocalTerm a c x = 0 := by
  have hu : Real.exp (2 * a) < x⁻¹ := by
    have h := (inv_lt_inv₀ (Real.exp_pos (-2 * a)) hx).mpr hsmall
    rw [show -2 * a = -(2 * a) by ring, Real.exp_neg, inv_inv] at h
    exact h
  have he : Real.exp (-2 * a) ≤ Real.exp (2 * a) := Real.exp_le_exp.mpr (by linarith only [ha])
  have h0 : 1 < x⁻¹ := (Real.one_le_exp (by linarith only [ha] : 0 ≤ 2 * a)).trans_lt hu
  unfold triangularGammaReciprocalTerm
  rw [triangular_profile_eq_zero_of_small_scale ha hx hsmall, Complex.ofReal_zero, zero_div,
    AnalyticNumberTheory.General.mellinResolventWeight_eq_zero_of_one_lt _
      ((one_lt_div (Real.exp_pos _)).mpr hu),
    AnalyticNumberTheory.General.mellinResolventWeight_eq_zero_of_one_lt _
      ((one_lt_div (Real.exp_pos _)).mpr (he.trans_lt hu)),
    AnalyticNumberTheory.General.mellinResolventWeight_eq_zero_of_one_lt _ h0]
  simp only [add_zero, mul_zero, sub_zero]

/-- For every character, positive parameter and scale below exp(-2a), the normalized
central Gamma integral vanishes. Its profile and every explicit reciprocal term vanish.
No GRH is needed. This evaluates the exterior branch before transferring to a right line. -/
theorem triangular_central_gammaIntegral_eq_zero_of_small_scale {q : ℕ} (χ : DirichletCharacter ℂ q)
    {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hsmall : x < Real.exp (-2 * a)) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction a (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) =
      0 := by
  obtain ⟨b, hb, _, hg⟩ := triangular_central_gammaIntegral_eq_weight_series χ
  have hs : (∑' n : ℕ, triangularGammaReciprocalTerm a (b + n) x) = 0 := by
    simp only [triangularGammaReciprocalTerm_eq_zero_of_small_scale ha hx hsmall, tsum_zero]
  rw [hg a x ha hx, triangular_profile_eq_zero_of_small_scale ha hx hsmall, Complex.ofReal_zero,
    mul_zero, hs, mul_zero, add_zero]

end PseudoPrime.LLS.PaperStatements
