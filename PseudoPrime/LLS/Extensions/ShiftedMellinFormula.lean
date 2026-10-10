/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.GammaPoleMellin
public import PseudoPrime.LLS.Extensions.CompletedZeroMellin
public import PseudoPrime.LLS.Extensions.RealAxisIntegration
public import PseudoPrime.LLS.Extensions.MangoldtSeries

/-!
# Exact shifted logarithmic formula for admissible general L-functions

Arithmetic Mellin inversion, completed-zero residues and gamma-pole residues give the formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- For L-function data f and real parameters x,σ,τ,y, sum the centered resolvent
kernels at the completed zeros shifted by σ, weighted by their analytic multiplicities.
Under individual RH and σ ≥ 1 the shifted poles lie in the left half-plane.
This is the zero contribution to the ordinary logarithmic-derivative integrand. -/
noncomputable def zeroResolventMellinIntegrand (f : GeneralLFunction) (x σ τ y : ℝ) : ℂ :=
  ∑' ρ : f.Zero,
    (analyticOrderNatAt f.completed (ρ : ℂ) : ℂ) *
      AnalyticNumberTheory.General.centeredResolventKernel ((ρ : ℂ) - (σ : ℂ)) x τ y

/-- For L-function data f and real parameters x,σ,τ,y, sum centered resolvent kernels
over all gamma factors and their poles -σ-κj-2n, with n a natural index.
If Re κj ≥ 0 and σ ≥ 1, these poles lie in the left half-plane.
This is the gamma contribution to the ordinary logarithmic-derivative integrand. -/
noncomputable def gammaResolventMellinIntegrand (f : GeneralLFunction) (x σ τ y : ℝ) : ℂ :=
  ∑ j : Fin f.degree,
    ∑' n : ℕ,
      AnalyticNumberTheory.General.centeredResolventKernel (-((σ : ℂ) + f.shift j + 2 * (n : ℂ))) x
        τ y

/-- For admissible RH data, σ ≥ 1 and positive τ,x, the zero Mellin series is integrable.
Use the three-halves shifted zero-mass convergence and the centered-resolvent bound.
This permits splitting the ordinary vertical integral into its analytic contributions. -/
theorem integrable_zeroResolventMellinIntegrand (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 0 < x) :
    MeasureTheory.Integrable (f.zeroResolventMellinIntegrand x σ τ) := by
  exact
    AnalyticNumberTheory.General.integrable_tsum_centeredResolventKernel
      (fun ρ : f.Zero ↦ (ρ : ℂ) - (σ : ℂ)) (fun ρ : f.Zero ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.ofReal_re, hRH ρ]; linarith only [hσ])
      hτ hx
      (summable_shifted_power_mass_of_admissible f hf hRH hσ
        (show (1 : ℝ) < 3 / 2 by norm_num only))

/-- For admissible shifts, σ ≥ 1 and positive τ,x, each gamma-factor Mellin series is
integrable. Apply the three-halves gamma-pole mass bound to the centered-resolvent theorem.
This justifies integrating the finite gamma family. -/
theorem integrable_gammaPoleMellinSeries (f : GeneralLFunction) (hf : f.IsAdmissible) {σ τ x : ℝ}
    (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 0 < x) (j : Fin f.degree) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        ∑' n : ℕ,
          AnalyticNumberTheory.General.centeredResolventKernel
            (-((σ : ℂ) + f.shift j + 2 * (n : ℂ))) x τ y) := by
  have hi :=
    AnalyticNumberTheory.General.integrable_tsum_centeredResolventKernel
      (fun n : ℕ ↦ -((σ : ℂ) + f.shift j + 2 * (n : ℂ))) (fun _ ↦ 1)
      (fun n ↦ by
        simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.re_ofNat, Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero,
          sub_zero]
        linarith only [hσ, hf.2.2.2.1 j, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))])
      hτ hx
      (by
        simpa only [Nat.cast_one] using
          (AnalyticNumberTheory.Gamma.summable_gammaPole_power_mass (hf.2.2.2.1 j) hσ
            (show (1 : ℝ) < 3 / 2 by norm_num only)))
  simpa only [Nat.cast_one, one_mul] using hi

/-- For admissible data, σ ≥ 1 and positive τ,x, the finite gamma Mellin family is integrable.
Sum the individual integrable gamma-factor series.
This supplies the gamma-side hypothesis for subtraction of Bochner integrals. -/
theorem integrable_gammaResolventMellinIntegrand (f : GeneralLFunction) (hf : f.IsAdmissible)
    {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 0 < x) :
    MeasureTheory.Integrable (f.gammaResolventMellinIntegrand x σ τ) :=
  MeasureTheory.integrable_finsetSum Finset.univ
    (fun j _ ↦ integrable_gammaPoleMellinSeries f hf hσ hτ hx j)

/-- For admissible data, real σ ≥ 1, τ > 0, and x > 1, the normalized gamma Mellin
integral equals shiftedGammaSum minus the derivative of the completion factor's
logarithmic derivative at σ. Integrate the finite family and apply the individual
pole evaluations. This identifies the gamma residues and their origin correction. -/
theorem normalized_integral_gammaResolventMellinIntegrand_eq (f : GeneralLFunction)
    (hf : f.IsAdmissible) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.gammaResolventMellinIntegrand x σ τ y) =
      f.shiftedGammaSum x σ - deriv (logDeriv f.completionFactor) (σ : ℂ) := by
  unfold gammaResolventMellinIntegrand
  rw [MeasureTheory.integral_finsetSum Finset.univ
      (fun j _ ↦ integrable_gammaPoleMellinSeries f hf hσ hτ (zero_lt_one.trans hx) j),
    Finset.smul_sum]
  exact sum_normalized_integral_gammaPoleResolvent_eq f hf hσ hτ hx

/-- For admissible data satisfying individual RH, real σ ≥ 1, τ > 0, and any real x,
the zero Mellin integrand equals the completed logarithmic derivative difference
between σ+z and σ, multiplied by x^z/z², where z = τ+i y.
Rewrite the zero-subtype Hadamard expansion at these two points.
This identifies the centered zero series in the completed logarithmic derivative. -/
theorem zeroResolventMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (y : ℝ) :
    f.zeroResolventMellinIntegrand x σ τ y =
      (logDeriv f.completed ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) - logDeriv f.completed (σ : ℂ)) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have hs : 1 / 2 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [hσ, hτ]
  have ht : 1 / 2 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]; linarith only [hσ]
  rw [zeroResolventMellinIntegrand,
    AnalyticNumberTheory.General.tsum_centeredResolventKernel_eq_difference
      (fun ρ : f.Zero ↦ (ρ : ℂ) - (σ : ℂ)) (fun ρ : f.Zero ↦ analyticOrderNatAt f.completed (ρ : ℂ))
      (fun ρ ↦ by
        rw [Complex.sub_re, Complex.ofReal_re, hRH ρ]; linarith only [hσ])
      hτ,
    logDeriv_completed_sub_eq_zeroSubtypeSeries f hf hRH hs ht]
  congr 2
  apply tsum_congr
  intro ρ
  have ha :
    (σ : ℂ) + ((τ : ℂ) + y * Complex.I) - (ρ : ℂ) =
      (τ : ℂ) + y * Complex.I - ((ρ : ℂ) - (σ : ℂ)) := by
    ring
  rw [ha, show (σ : ℂ) - (ρ : ℂ) = -((ρ : ℂ) - (σ : ℂ)) by ring]
  simp only [one_div, inv_neg, sub_neg_eq_add]

/-- For admissible data, σ ≥ 1 and τ > 0, the gamma Mellin series is minus the completion
logarithmic-derivative difference times x^z/z². Rewrite the digamma reciprocal differences
at the shifted gamma poles. This supplies the gamma part of the integrand decomposition. -/
theorem gammaResolventMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible) {σ τ x : ℝ}
    (hσ : 1 ≤ σ) (hτ : 0 < τ) (y : ℝ) :
    f.gammaResolventMellinIntegrand x σ τ y =
      -(logDeriv f.completionFactor ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) -
              logDeriv f.completionFactor (σ : ℂ)) *
          (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 := by
  have hs : 0 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [hσ, hτ]
  have ht : 0 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]; linarith only [hσ]
  rw [logDeriv_completionFactor_sub_eq_gammaPoleSeries f hf hs ht, ← Finset.sum_neg_distrib,
    Finset.sum_mul, Finset.sum_div]
  unfold gammaResolventMellinIntegrand
  apply Finset.sum_congr rfl
  intro j _
  rw [← tsum_neg, ← tsum_mul_right, ← tsum_div_const]
  apply tsum_congr
  intro n
  have hα : (-((σ : ℂ) + f.shift j + 2 * (n : ℂ))).re < 0 := by
    simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat,
      Complex.natCast_re, Complex.im_ofNat, Complex.natCast_im, mul_zero, sub_zero]
    linarith only [hσ, hf.2.2.2.1 j, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
  rw [AnalyticNumberTheory.General.centeredResolventKernel_eq_difference hα hτ]
  have ha :
    (σ : ℂ) + ((τ : ℂ) + y * Complex.I) + f.shift j + 2 * (n : ℂ) =
      ((τ : ℂ) + y * Complex.I) + ((σ : ℂ) + f.shift j + 2 * (n : ℂ)) := by
    ring
  rw [ha]
  simp only [sub_neg_eq_add, one_div, inv_neg]
  ring

/-- For admissible data satisfying individual RH and real σ ≥ 1, the derivative
of the ordinary logarithmic derivative equals the completed logarithmic derivative's
derivative minus the completion factor's logarithmic derivative's derivative at σ.
Differentiate the local completion identity; analyticity and nonvanishing justify
the quotient derivatives. This combines the zero and gamma origin corrections. -/
theorem deriv_logDeriv_ordinary_eq_completed_sub_completionFactor (f : GeneralLFunction)
    (hf : f.IsAdmissible) (hRH : f.RiemannHypothesis) {σ : ℝ} (hσ : 1 ≤ σ) :
    deriv (logDeriv f.L) (σ : ℂ) =
      deriv (logDeriv f.completed) (σ : ℂ) - deriv (logDeriv f.completionFactor) (σ : ℂ) := by
  have hs : 1 / 2 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]; linarith only [hσ]
  have he :
    logDeriv f.completionFactor =ᶠ[nhds (σ : ℂ)]
      (fun s : ℂ ↦ logDeriv f.completed s - logDeriv f.L s) := by
    filter_upwards [Complex.continuous_re.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hs)] with s
      hs'
    have h :=
      logDeriv_completed_eq_completionFactor_add f hf
        (lt_trans (show (0 : ℝ) < 1 / 2 by norm_num only) hs')
        (completed_ne_zero_of_re_ne_half hRH hs'.ne')
    linear_combination -h
  have hF := (hf.2.2.2.2.2.2.2.1 : Differentiable ℂ f.completed).analyticAt (σ : ℂ)
  have hn := completed_ne_zero_of_re_ne_half hRH hs.ne'
  have hDc : AnalyticAt ℂ (logDeriv f.completed) (σ : ℂ) := hF.deriv.div hF hn
  have hDo := analyticAt_logDeriv_ordinary_of_re_gt_half f hf hRH hs
  have hd := he.deriv_eq
  change
    deriv (logDeriv f.completionFactor) (σ : ℂ) =
      deriv (logDeriv f.completed - logDeriv f.L) (σ : ℂ) at hd
  rw [deriv_sub hDc.differentiableAt hDo.differentiableAt] at hd
  rw [hd]
  ring

/-- For admissible RH data, σ ≥ 1 and τ > 0, the negative ordinary logarithmic-derivative
Mellin integrand splits into its constant term minus the zero and gamma centered series.
Use the two reciprocal expansions and the completion product identity.
This is the pointwise decomposition of the arithmetic Mellin integrand. -/
theorem ordinaryMellinIntegrand_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (y : ℝ) :
    -logDeriv f.L ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
        ((τ : ℂ) + y * Complex.I) ^ 2 =
      -logDeriv f.L (σ : ℂ) *
          ((x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2) -
        f.zeroResolventMellinIntegrand x σ τ y -
        f.gammaResolventMellinIntegrand x σ τ y := by
  have hs : 1 / 2 < ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_self, add_zero]
    linarith only [hσ, hτ]
  have ht : 1 / 2 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]; linarith only [hσ]
  rw [zeroResolventMellinIntegrand_eq f hf hRH hσ hτ, gammaResolventMellinIntegrand_eq f hf hσ hτ,
    logDeriv_completed_eq_completionFactor_add f hf
      (lt_trans (show (0 : ℝ) < 1 / 2 by norm_num only) hs)
      (completed_ne_zero_of_re_ne_half hRH hs.ne'),
    logDeriv_completed_eq_completionFactor_add f hf
      (lt_trans (show (0 : ℝ) < 1 / 2 by norm_num only) ht)
      (completed_ne_zero_of_re_ne_half hRH ht.ne')]
  ring

/-- For admissible RH data, σ ≥ 1, τ > 0 and x > 1, the normalized ordinary Mellin integral
is the regularized origin derivative plus the shifted zero sum minus the gamma sum.
All three parts are integrable; their evaluated residues and origin derivatives combine
by the differentiated completion identity. This proves the analytic shifted formula. -/
theorem normalized_integral_ordinaryMellin_eq (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ τ x : ℝ} (hσ : 1 ≤ σ) (hτ : 0 < τ) (hx : 1 < x) :
    (2 * Real.pi)⁻¹ •
        (∫ y : ℝ,
          -logDeriv f.L ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
            ((τ : ℂ) + y * Complex.I) ^ 2) =
      deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ)) 0 +
          f.shiftedZeroSum x σ -
        f.shiftedGammaSum x σ := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  obtain ⟨hG, hGI⟩ := AnalyticNumberTheory.General.logarithmicMellin_integrable_and_integral hτ hx
  have hO := hG.const_mul (-logDeriv f.L (σ : ℂ))
  have hZ := integrable_zeroResolventMellinIntegrand f hf hRH hσ hτ hx0
  have hΓ := integrable_gammaResolventMellinIntegrand f hf hσ hτ hx0
  have he :
    (fun y : ℝ ↦
        -logDeriv f.L ((σ : ℂ) + ((τ : ℂ) + y * Complex.I)) * (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) /
          ((τ : ℂ) + y * Complex.I) ^ 2) =
      (fun y : ℝ ↦
        -logDeriv f.L (σ : ℂ) *
            ((x : ℂ) ^ ((τ : ℂ) + y * Complex.I) / ((τ : ℂ) + y * Complex.I) ^ 2) -
          f.zeroResolventMellinIntegrand x σ τ y -
          f.gammaResolventMellinIntegrand x σ τ y) :=
    funext (ordinaryMellinIntegrand_eq f hf hRH hσ hτ)
  have hZI :
    (2 * Real.pi)⁻¹ • (∫ y : ℝ, f.zeroResolventMellinIntegrand x σ τ y) =
      -f.shiftedZeroSum x σ + deriv (logDeriv f.completed) (σ : ℂ) :=
    normalized_integral_zeroResolvent_eq f hf hRH hσ hτ hx
  have hIZΓ := MeasureTheory.integral_sub (hO.sub hZ) hΓ
  simp only [Pi.sub_apply] at hIZΓ
  have hIZ := MeasureTheory.integral_sub hO hZ
  rw [he, hIZΓ, hIZ, smul_sub, smul_sub, MeasureTheory.integral_const_mul, ← mul_smul_comm, hGI,
    hZI, normalized_integral_gammaResolventMellinIntegrand_eq f hf hσ hτ hx]
  have hs : 1 / 2 < (σ : ℂ).re := by
    rw [Complex.ofReal_re]; linarith only [hσ]
  rw [AnalyticNumberTheory.General.deriv_shiftedLogarithmicRegularization
      (analyticAt_ordinary_of_re_pos f hf (lt_trans (show (0 : ℝ) < 1 / 2 by norm_num only) hs))
      (ordinary_ne_zero_of_re_gt_half f hf hRH hs) hx0,
    deriv_logDeriv_ordinary_eq_completed_sub_completionFactor f hf hRH hσ]
  ring

/-- For admissible RH data, σ > 1 and x > 1, the shifted weighted arithmetic sum equals
the regularized origin derivative plus the shifted zero sum minus the gamma sum.
Combine arithmetic Mellin inversion on the line τ=1 with the analytic integral evaluation.
This discharges the exact-formula input to the generalized logarithmic Lemma 2.5. -/
theorem shiftedArithmeticSum_eq_origin_zero_sub_gamma (f : GeneralLFunction) (hf : f.IsAdmissible)
    (hRH : f.RiemannHypothesis) {σ x : ℝ} (hσ : 1 < σ) (hx : 1 < x) :
    f.shiftedArithmeticSum x σ =
      deriv (AnalyticNumberTheory.General.shiftedLogarithmicRegularization f.L x (σ : ℂ)) 0 +
          f.shiftedZeroSum x σ -
        f.shiftedGammaSum x σ := by
  rw [shiftedArithmeticSum_eq_integral_logDeriv f hf hσ (zero_lt_one.trans hx)
      (show (0 : ℝ) < 1 by norm_num only)]
  simp only [Complex.ofReal_add, add_assoc]
  exact normalized_integral_ordinaryMellin_eq f hf hRH hσ.le zero_lt_one hx

end PseudoPrime.LLS.Extensions.GeneralLFunction
