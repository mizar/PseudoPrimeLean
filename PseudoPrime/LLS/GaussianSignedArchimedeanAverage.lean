/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianMellinAverage
public import PseudoPrime.LLS.GaussianArchimedeanBounds
public import PseudoPrime.LLS.GammaArchimedeanSign

/-! # Signed Gaussian average of the Gamma archimedean term

Transfer the scale-dependent sign of the unsmoothed Gamma term through the
logarithmic Gaussian average. -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The normalized unsmoothed central Gamma archimedean integral at scale x. -/
noncomputable def gammaCentralArchimedeanIntegral {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)

/-- The normalized central Gamma archimedean integral with the Gaussian
multiplier. -/
noncomputable def gaussianCentralArchimedeanIntegral {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))

/-- Scaling the input of the unsmoothed central Gamma integral inserts the
vertical Mellin exponential. -/
theorem gammaCentralArchimedeanIntegral_logScale {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) (v : ℝ) :
    gammaCentralArchimedeanIntegral χ (x * Real.exp v) =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          Complex.exp ((Complex.I * (t : ℂ)) * (v : ℂ)) *
            (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)) := by
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            gammaCentralMellinWeight (x * Real.exp v) t) =
      _
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact
    Filter.Eventually.of_forall fun t => by
      change
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            gammaCentralMellinWeight (x * Real.exp v) t =
          Complex.exp ((Complex.I * (t : ℂ)) * (v : ℂ)) *
            (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)
      unfold gammaCentralMellinWeight
      have hc := gaussian_cpow_scale hx (-v) (-(Complex.I * (t : ℂ)))
      have hv : (↑(-v) : ℂ) = -(v : ℂ) := by rw [Complex.ofReal_neg]
      rw [hv, neg_mul_neg, neg_neg, neg_neg] at hc
      rw [hc.symm]
      ring_nf

/-- The Gaussian central Gamma term is the logarithmic Gaussian average of
the unsmoothed central term. Fubini applies to the absolutely integrable
vertical Gamma integrand. -/
theorem gaussianCentralArchimedeanIntegral_eq_logGaussianAverage {q : ℕ}
    (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    gaussianCentralArchimedeanIntegral χ x =
      ∫ v : ℝ,
        (Analysis.normalizedGaussianWeight v : ℂ) *
          gammaCentralArchimedeanIntegral χ (x * Real.exp v) := by
  let F : ℝ → ℂ := fun t =>
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t
  have hF : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gammaMellinKernel χ (c := 0) (by norm_num only)
        (by linarith only [gammaMellinKernel.delta_pos]) (by norm_num only) hx
    simpa only [F, gammaCentralMellinWeight, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hline (t : ℝ) :
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) =
      Complex.exp (((Complex.I * (t : ℂ)) ^ 2) / 4) * F t := by
    change
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          ((gammaMellinKernel.function (Complex.I * t) *
              Complex.exp ((Complex.I * (t : ℂ)) ^ 2 / 4)) *
            (x : ℂ) ^ (Complex.I * t)) =
        Complex.exp (((Complex.I * (t : ℂ)) ^ 2) / 4) *
          (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))
    ring_nf
  have hgauss :
    (∫ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) =
      ∫ t : ℝ, Complex.exp (((Complex.I * (t : ℂ)) ^ 2) / 4) * F t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hline)
  calc
    _ =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, Complex.exp (((Complex.I * (t : ℂ)) ^ 2) / 4) * F t) :=
      by rw [gaussianCentralArchimedeanIntegral, hgauss]
    _ =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ v : ℝ,
            (Analysis.normalizedGaussianWeight v : ℂ) *
              (∫ t : ℝ, Complex.exp ((Complex.I * (t : ℂ)) * (v : ℂ)) * F t)) :=
      by
      have havg := integral_gaussianMultiplier_eq_logGaussianAverage (c := 0) hF
      simpa only [Complex.ofReal_zero, zero_add] using congrArg _ havg
    _ =
        ∫ v : ℝ,
          (Analysis.normalizedGaussianWeight v : ℂ) *
            gammaCentralArchimedeanIntegral χ (x * Real.exp v) :=
      by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall fun v => by
          change
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                ((Analysis.normalizedGaussianWeight v : ℂ) *
                  (∫ t : ℝ, Complex.exp ((Complex.I * (t : ℂ)) * (v : ℂ)) * F t)) =
              (Analysis.normalizedGaussianWeight v : ℂ) *
                gammaCentralArchimedeanIntegral χ (x * Real.exp v)
          rw [gammaCentralArchimedeanIntegral_logScale χ hx v]
          dsimp only [F]
          have hint :
            (∫ t : ℝ,
                Complex.exp ((Complex.I * (t : ℂ)) * (v : ℂ)) *
                  (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)) =
              ∫ t : ℝ,
                Complex.exp ((Complex.I * (v : ℂ)) * (t : ℂ)) *
                  (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                    gammaCentralMellinWeight x t) := by
            apply MeasureTheory.integral_congr_ae
            exact Filter.Eventually.of_forall fun t => by ring_nf
          rw [hint]
          ring_nf

/-- The real part of the unsmoothed central archimedean term is bounded by
128/(9x), using its nonpositive sign from scale two and its uniform norm bound
below scale two. -/
theorem re_gammaCentralArchimedeanIntegral_le_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : (gammaCentralArchimedeanIntegral χ x).re ≤ (128 / 9 : ℝ) / x := by
  by_cases htwo : 2 ≤ x
  · have hs := gamma_central_archimedean_integral_re_nonpos χ htwo
    dsimp only [gammaCentralArchimedeanIntegral] at hs ⊢
    exact hs.trans (by positivity)
  · have hsmall : x < 2 := lt_of_not_ge htwo
    have hn := norm_gamma_central_integral_le_sixty_four_ninths χ hx
    have hre := Complex.re_le_norm (gammaCentralArchimedeanIntegral χ x)
    dsimp only [gammaCentralArchimedeanIntegral] at hn ⊢
    have hcap : (64 / 9 : ℝ) ≤ (128 / 9 : ℝ) / x := by
      rw [le_div_iff₀ hx]
      nlinarith only [hsmall]
    exact (hre.trans hn).trans hcap

/-- The Gaussian archimedean term inherits the inverse-scale estimate after
averaging the pointwise sign and norm bounds. -/
theorem re_gaussianCentralArchimedeanIntegral_le_inv {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) : (gaussianCentralArchimedeanIntegral χ x).re ≤ (512 / 27 : ℝ) / x := by
  rw [gaussianCentralArchimedeanIntegral_eq_logGaussianAverage χ hx]
  let G : ℝ → ℂ := fun v =>
    (Analysis.normalizedGaussianWeight v : ℂ) * gammaCentralArchimedeanIntegral χ (x * Real.exp v)
  let F : ℝ → ℂ := fun t =>
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t
  have hF : MeasureTheory.Integrable F := by
    have hi :=
      MellinKernel.integrable_gammaFactor_power_line gammaMellinKernel χ (c := 0) (by norm_num only)
        (by linarith only [gammaMellinKernel.delta_pos]) (by norm_num only) hx
    simpa only [F, gammaCentralMellinWeight, Complex.ofReal_zero, zero_add, mul_assoc] using hi
  have hH := integrable_logGaussianAverage_integrand (c := 0) hF
  have hG : MeasureTheory.Integrable G := by
    apply (hH.const_mul ((1 / (2 * Real.pi) : ℝ) : ℂ)).congr
    filter_upwards with v
    dsimp only [G]
    rw [gammaCentralArchimedeanIntegral_logScale χ hx v]
    have hint :
      (∫ t : ℝ, Complex.exp ((((0 : ℝ) : ℂ) + Complex.I * (t : ℂ)) * (v : ℂ)) * F t) =
        ∫ t : ℝ,
          Complex.exp ((Complex.I * (v : ℂ)) * (t : ℂ)) *
            (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t) := by
      apply MeasureTheory.integral_congr_ae
      exact
        Filter.Eventually.of_forall fun t => by
          dsimp only [F]
          simp only [Complex.ofReal_zero, zero_add]
          ring_nf
    rw [hint]
    ring_nf
  have hRe := Complex.reCLM.integrable_comp hG
  have hpoint (v : ℝ) :
    (G v).re ≤ Analysis.normalizedGaussianWeight v * ((128 / 9 : ℝ) / (x * Real.exp v)) := by
    dsimp only [G]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact
      mul_le_mul_of_nonneg_left
        (re_gammaCentralArchimedeanIntegral_le_inv χ (mul_pos hx (Real.exp_pos v)))
        (Analysis.normalizedGaussianWeight_pos v).le
  have hfactor (v : ℝ) :
    Analysis.normalizedGaussianWeight v * ((128 / 9 : ℝ) / (x * Real.exp v)) =
      ((128 / 9 : ℝ) / x) * (Analysis.normalizedGaussianWeight v * Real.exp (-v)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, Real.exp_neg]
    field_simp
  have hupper :
    MeasureTheory.Integrable
      (fun v : ℝ => Analysis.normalizedGaussianWeight v * ((128 / 9 : ℝ) / (x * Real.exp v))) := by
    have hi := (Analysis.integrable_normalizedGaussian_mul_exp (-1)).const_mul ((128 / 9 : ℝ) / x)
    apply hi.congr
    filter_upwards with v
    simpa only [neg_one_mul] using (hfactor v).symm
  have hmono := MeasureTheory.integral_mono hRe hupper hpoint
  have he := Complex.reCLM.integral_comp_comm hG
  have hmoment := Analysis.integral_normalizedGaussian_mul_exp (-1)
  have hmoment' :
    (∫ v : ℝ, Analysis.normalizedGaussianWeight v * Real.exp (-v)) = Real.exp (1 / 4 : ℝ) := by
    have hsq : (-1 : ℝ) ^ 2 / 4 = 1 / 4 := by norm_num only
    rw [hsq] at hmoment
    simpa only [neg_one_mul] using hmoment
  have hlog : (1 / 4 : ℝ) ≤ Real.log (4 / 3) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 3 / 4)
    have hid : Real.log (4 / 3 : ℝ) = -Real.log (3 / 4 : ℝ) := by
      calc
        Real.log (4 / 3 : ℝ) = -Real.log ((4 / 3 : ℝ)⁻¹) := by
          rw [Real.log_inv]
          ring
        _ = -Real.log (3 / 4 : ℝ) := by
          congr 1; norm_num only
    nlinarith only [h, hid]
  have hexp : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    calc
      Real.exp (1 / 4 : ℝ) ≤ Real.exp (Real.log (4 / 3)) := Real.exp_le_exp.mpr hlog
      _ = 4 / 3 := by
        rw [Real.exp_log]; norm_num only
  calc
    (∫ v : ℝ, G v).re = ∫ v : ℝ, (G v).re := he.symm
    _ ≤ ∫ v : ℝ, Analysis.normalizedGaussianWeight v * ((128 / 9 : ℝ) / (x * Real.exp v)) := hmono
    _ = ((128 / 9 : ℝ) / x) * Real.exp (1 / 4 : ℝ) := by
      have hint :
        (∫ v : ℝ, Analysis.normalizedGaussianWeight v * ((128 / 9 : ℝ) / (x * Real.exp v))) =
          ∫ v : ℝ, ((128 / 9 : ℝ) / x) * (Analysis.normalizedGaussianWeight v * Real.exp (-v)) := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hfactor
      rw [hint, MeasureTheory.integral_const_mul, hmoment']
    _ ≤ (512 / 27 : ℝ) / x := by
      have hcoef : (128 / 9 : ℝ) * Real.exp (1 / 4 : ℝ) ≤ 512 / 27 := by
        calc
          (128 / 9 : ℝ) * Real.exp (1 / 4 : ℝ) ≤ (128 / 9 : ℝ) * (4 / 3) :=
            mul_le_mul_of_nonneg_left hexp (by norm_num only)
          _ = 512 / 27 := by norm_num only
      calc
        ((128 / 9 : ℝ) / x) * Real.exp (1 / 4 : ℝ) = ((128 / 9 : ℝ) * Real.exp (1 / 4 : ℝ)) * x⁻¹ :=
          by ring
        _ ≤ (512 / 27 : ℝ) * x⁻¹ := mul_le_mul_of_nonneg_right hcoef (inv_nonneg.mpr hx.le)
        _ = (512 / 27 : ℝ) / x := by ring

/-- The completed Gaussian remainder is bounded in real part by the
scale-dependent signed archimedean estimate. -/
theorem re_gaussian_completed_remainder_le_inv {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {a b x : ℝ} (hab : a < b)
    (ha : -1 / 2 - gaussianGammaMellinKernel.delta < a)
    (hb : b ≤ 1 / 2 + gaussianGammaMellinKernel.delta) (ha' : -3 / 2 ≤ a) (hb' : b ≤ 3 / 2)
    (hx : 1 ≤ x) (hal : a < -1 / 2) (hbr : 1 / 2 < b) :
    ((∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) -
          (MellinKernel.weightedResidue gaussianGammaMellinKernel
                (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
              (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ) +
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
              (∫ t : ℝ,
                -logDeriv χ.completedLFunction (((a : ℂ) + Complex.I * t) + 1 / 2) *
                  (gaussianGammaMellinKernel.function ((a : ℂ) + Complex.I * t) *
                    (x : ℂ) ^ ((a : ℂ) + Complex.I * t))))).re ≤
      (512 / 27 : ℝ) / x := by
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  obtain ⟨c, hc⟩ := χ.conductor_dvd_level
  have hdiv : χ.conductor ∣ q := ⟨c, hc⟩
  have hmq : χ.conductor ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdiv
  have hq : 2 ≤ q := (by norm_num only : 2 ≤ 3).trans (hm.trans hmq)
  have h :=
    MellinKernel.tsum_summand_eq_completed_residue_formula gaussianGammaMellinKernel hq hGRH hp hne
      hinv hab ha hb ha' hb' hx hal hbr
  dsimp only at h
  rw [h, add_sub_cancel_left]
  rw [MellinKernel.gammaIntegral_eq_central gaussianGammaMellinKernel χ (by linarith only [hbr]) hb
      hb' hx]
  change (gaussianCentralArchimedeanIntegral χ x).re ≤ _
  exact re_gaussianCentralArchimedeanIntegral_le_inv χ (zero_lt_one.trans_le hx)

end PseudoPrime.LLS.PaperStatements
