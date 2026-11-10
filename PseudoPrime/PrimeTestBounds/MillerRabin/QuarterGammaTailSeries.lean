/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaConvolutionSplit

/-! # Termwise integration of the even Gamma tail -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The term after the first pole in the even digamma correction, multiplied by the
real oscillatory phase. Its index starts at the pole with rate `5/2`. -/
noncomputable def quarterGammaTailTerm (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((t / 2) ^ 2 / ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2))) *
    target028GammaPhase y t

/-- Each signed tail term is absolutely bounded by the second kernel moment times
the corresponding inverse cube. This is the majorant for termwise integration. -/
theorem quarter_gamma_tail_term_bound (y : ℝ) (n : ℕ) (t : ℝ) :
    ‖quarterGammaTailTerm y n t‖ ≤
      (2 / (2 * (n : ℝ) + 5 / 2) ^ 3) *
        (t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖) := by
  have ha : 0 < (1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ) := by positivity
  have hd :
    0 ≤
      (t / 2) ^ 2 /
        ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg ha.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hp : |target028GammaPhase y t| ≤ ‖refinedSixPoleKernel.function (Complex.I * t)‖ := by
    have h :=
      Complex.abs_re_le_norm
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y))
    rw [norm_mul, Complex.norm_exp] at h
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero, mul_one] at h
    exact h
  rw [quarterGammaTailTerm, norm_mul, Real.norm_eq_abs, abs_of_nonneg hd, Real.norm_eq_abs]
  have h :=
    mul_le_mul (target028_gamma_correction_term t n) hp (abs_nonneg _)
      (le_trans hd (target028_gamma_correction_term t n))
  convert h using 1
  ring

/-- Each tail term is integrable: its continuous integrand is dominated by the
integrable second moment of the sixth-pole kernel. -/
theorem quarter_gamma_tail_term_integrable (y : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (quarterGammaTailTerm y n) := by
  have hd (t : ℝ) :
    (1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2) ≠ 0 := by
    positivity
  have hc : Continuous (quarterGammaTailTerm y n) := by
    unfold quarterGammaTailTerm
    apply Continuous.mul
    · exact
        ((continuous_id.div_const 2).pow 2).div
          (continuous_const.mul (continuous_const.add ((continuous_id.div_const 2).pow 2))) hd
    · exact (target028_gamma_phase_integrable y).1
  apply
    (refined_six_pole_second_integrable.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)).mono'
      hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (quarter_gamma_tail_term_bound y n)

/-- The integrals of the absolute tail terms form a convergent series, using the
summable inverse-cube bound for the pole rates. -/
theorem quarter_gamma_tail_norm_summable (y : ℝ) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖quarterGammaTailTerm y n t‖) := by
  let C : ℝ := ∫ t : ℝ, t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖
  have hs : Summable (fun n : ℕ ↦ (2 * C) * (1 / (2 * (n : ℝ) + 5 / 2) ^ 3)) :=
    target028_gamma_pole_tail_summable.mul_left (2 * C)
  apply hs.of_nonneg_of_le
  · intro n
    exact MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _)
  · intro n
    have hi := quarter_gamma_tail_term_integrable y n
    have hmajor := refined_six_pole_second_integrable.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)
    have h := MeasureTheory.integral_mono hi.norm hmajor (quarter_gamma_tail_term_bound y n)
    rw [MeasureTheory.integral_const_mul] at h
    dsimp only [C]
    convert h using 1
    ring

/-- The oscillatory even-Gamma tail can be integrated term by term: the individual
terms are integrable and their integral norms form a summable series. -/
theorem quarter_gamma_tail_integral_tsum (y : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, quarterGammaTailTerm y n t) =
      ∑' n : ℕ, ∫ t : ℝ, quarterGammaTailTerm y n t := by
  exact
    (MeasureTheory.integral_tsum_of_summable_integral_norm (quarter_gamma_tail_term_integrable y)
        (quarter_gamma_tail_norm_summable y)).symm

/-- For a positive pole rate, the real phase resolvent is the real part of the
complex resolvent integral. The reciprocal denominator is bounded by `1 / c²`. -/
theorem quarter_phase_resolvent_general (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, target028GammaPhase y t / (c ^ 2 + t ^ 2)) =
      (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hcont : Continuous (fun t : ℝ ↦ (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t ↦ (hden t).ne'))
  have hi := (target028_gamma_phase_integrable y).2.2
  have hm := hi.mul_bdd (c := (c ^ 2)⁻¹) hcont.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (c ^ 2)⁻¹ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hden t).le)]
    exact inv_anti₀ (sq_pos_of_pos hc) (le_add_of_nonneg_right (sq_nonneg t))
  have hr := Complex.reCLM.integral_comp_comm (hm hb)
  change
    (∫ t : ℝ,
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) =
      _ at hr
  have he :
    (∫ t : ℝ, target028GammaPhase y t / (c ^ 2 + t ^ 2)) =
      ∫ t : ℝ,
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [target028GammaPhase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  rw [he, hr]
  simp only [one_div]
  rfl

/-- The normalized phase mass equals the shifted Gamma density. This is the
zero-pole Fourier inversion used to compare each correction with its resolvent. -/
theorem quarter_phase_mass_eq_density (y : ℝ) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, target028GammaPhase y t) =
      quarterGammaDensity (y + 21 / 8) := by
  have hr := Complex.reCLM.integral_comp_comm (target028_gamma_phase_integrable y).2.2
  change
    (∫ t : ℝ, target028GammaPhase y t) =
      (∫ t : ℝ,
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hr
  rw [hr]
  have h := congrArg Complex.re (quarter_kernel_fourier_eq y)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have he : (21 / 8 : ℝ) - (y + 21 / 8) = -y := by ring
  rw [← he, quarter_profile_shift] at h
  exact h

/-- Above the shifted scale twelve, the integral of each even-Gamma correction
after the first pole is nonpositive. The phase mass and resolvent are paired before
integration, avoiding a difference of divergent series. -/
theorem quarter_gamma_tail_term_integral_nonpos {y : ℝ} (hy : 12 ≤ y + 21 / 8) (n : ℕ) :
    (∫ t : ℝ, quarterGammaTailTerm y n t) ≤ 0 := by
  let c : ℝ := 2 * (n : ℝ) + 5 / 2
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hc0 : 0 < c := by linarith only [hc]
  have hden (t : ℝ) : c ^ 2 + t ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (sq_nonneg t)).ne'
  have he (t : ℝ) :
    quarterGammaTailTerm y n t =
      (2 / c) *
        (target028GammaPhase y t - c ^ 2 * (target028GammaPhase y t / (c ^ 2 + t ^ 2))) := by
    dsimp only [quarterGammaTailTerm, c]
    push_cast
    field_simp
    ring
  have hr (t : ℝ) :
    target028GammaPhase y t / (c ^ 2 + t ^ 2) =
      (c ^ 2)⁻¹ * (target028GammaPhase y t - (c / 2) * quarterGammaTailTerm y n t) := by
    rw [he]
    field_simp
    ring
  have hiP := (target028_gamma_phase_integrable y).2.1
  have hiF := quarter_gamma_tail_term_integrable y n
  have hiR : MeasureTheory.Integrable (fun t : ℝ ↦ target028GammaPhase y t / (c ^ 2 + t ^ 2)) := by
    apply ((hiP.sub (hiF.const_mul (c / 2))).const_mul (c ^ 2)⁻¹).congr
    exact Filter.Eventually.of_forall (fun t ↦ (hr t).symm)
  have hint :
    (∫ t : ℝ, quarterGammaTailTerm y n t) =
      (2 / c) *
        ((∫ t : ℝ, target028GammaPhase y t) -
          c ^ 2 * ∫ t : ℝ, target028GammaPhase y t / (c ^ 2 + t ^ 2)) := by
    have hfun :
      quarterGammaTailTerm y n = fun t ↦
        (2 / c) * (target028GammaPhase y t - c ^ 2 * (target028GammaPhase y t / (c ^ 2 + t ^ 2))) :=
      funext he
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hiP (hiR.const_mul _),
      MeasureTheory.integral_const_mul]
  have hpole := quarter_gamma_pole_ge_density hy hc
  rw [← quarter_phase_resolvent_general y hc0] at hpole
  rw [← quarter_phase_mass_eq_density y] at hpole
  have hpi : 0 < (1 / (2 * Real.pi) : ℝ) := by positivity
  have hcmp :
    (∫ t : ℝ, target028GammaPhase y t) ≤
      c ^ 2 * ∫ t : ℝ, target028GammaPhase y t / (c ^ 2 + t ^ 2) := by
    nlinarith only [hpole, hpi]
  rw [hint]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hcmp)

/-- Above the shifted scale twelve, the integrated even-Gamma tail after the
first pole is nonpositive. Absolute convergence permits termwise integration. -/
theorem quarter_gamma_tail_integral_nonpos {y : ℝ} (hy : 12 ≤ y + 21 / 8) :
    (∫ t : ℝ, ∑' n : ℕ, quarterGammaTailTerm y n t) ≤ 0 := by
  rw [quarter_gamma_tail_integral_tsum]
  exact tsum_nonpos (quarter_gamma_tail_term_integral_nonpos hy)

/-- The oscillatory digamma increment after removing its first pole equals the
convergent series of signed tail terms. The identity separates the first term of
the vertical digamma expansion and distributes the phase over the remaining sum. -/
theorem quarter_gamma_tail_eq_series (y t : ℝ) :
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        target028GammaPhase y t =
      ∑' n : ℕ, quarterGammaTailTerm y n t := by
  have h :=
    AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hs :=
    AnalyticNumberTheory.Gamma.summable_vertical_digamma_correction (a := (1 / 4 : ℝ)) (t := t / 2)
      (by norm_num only)
  have hfirst :
    (t / 2) ^ 2 / ((1 / 4 : ℝ) * ((1 / 4) ^ 2 + (t / 2) ^ 2)) = 4 - 1 / (1 / 4 + t ^ 2) := by
    have hp : 0 < 1 / 4 + t ^ 2 := by nlinarith only [sq_nonneg t]
    field_simp
    ring
  rw [hs.tsum_eq_zero_add] at h
  simp only [Nat.cast_zero, add_zero] at h
  rw [hfirst] at h
  simp only [quarterGammaTailTerm, tsum_mul_right]
  have he := congrArg (fun x : ℝ ↦ (x - (4 - 1 / (1 / 4 + t ^ 2))) * target028GammaPhase y t) h
  simpa only [add_sub_cancel_left, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using he

/-- At shifted scale at least twelve, the integrated vertical digamma correction
after its first pole is nonpositive. This combines the pointwise series identity
with the absolute convergence and polewise sign estimates. -/
theorem quarter_gamma_tail_signed {y : ℝ} (hy : 12 ≤ y + 21 / 8) :
    (∫ t : ℝ,
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
            (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
            (4 - 1 / (1 / 4 + t ^ 2))) *
          target028GammaPhase y t) ≤
      0 := by
  simpa only [quarter_gamma_tail_eq_series] using quarter_gamma_tail_integral_nonpos hy

/-- Above shifted scale twelve, the even-Gamma phase integral and first-pole
resolvent retain the negative baseline. The baseline is at most negative four
thirds times the nonnegative phase mass, and the remaining tail is nonpositive. -/
theorem quarter_gamma_phase_baseline {y : ℝ} (hy : 12 ≤ y + 21 / 8)
    (hG :
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            target028GammaPhase y t)) :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            target028GammaPhase y t) +
        (∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2)) ≤
      -(4 / 3 : ℝ) * (∫ t : ℝ, target028GammaPhase y t) := by
  let B : ℝ := (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re - Real.log Real.pi
  let P := target028GammaPhase y
  let E : ℝ → ℝ := fun t ↦
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t -
        (B + 4) * P t +
      P t / (1 / 4 + t ^ 2)
  have hP : MeasureTheory.Integrable P := (target028_gamma_phase_integrable y).2.1
  have hR : MeasureTheory.Integrable (fun t ↦ P t / (1 / 4 + t ^ 2)) :=
    target028_gamma_resolvent_integrable y
  have he (t : ℝ) :
    E t =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        P t := by
    dsimp only [E, B]
    ring
  have hneg : (∫ t : ℝ, E t) ≤ 0 := by simpa only [he, P] using quarter_gamma_tail_signed hy
  have hbase : B + 4 ≤ -(4 / 3 : ℝ) := by
    dsimp only [B]
    linarith only [LLS.PaperStatements.gamma_even_baseline_lt]
  have hmass := target028_gamma_phase_mass_nonneg y
  have hb := mul_le_mul_of_nonneg_right hbase hmass
  have heint :
    (∫ t : ℝ, E t) =
      (∫ t : ℝ,
            ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
              P t) -
          (B + 4) * (∫ t : ℝ, P t) +
        ∫ t : ℝ, P t / (1 / 4 + t ^ 2) := by
    dsimp only [E]
    have hadd := MeasureTheory.integral_add (hG.sub (hP.const_mul (B + 4))) hR
    have hsub := MeasureTheory.integral_sub hG (hP.const_mul (B + 4))
    simp only [Pi.sub_apply] at hadd hsub
    rw [hadd, hsub, MeasureTheory.integral_const_mul]
  dsimp only [P] at heint
  linarith only [heint, hb, hneg]

/-- Above shifted scale twelve, the even-Gamma phase integral and the first-pole
resolvent have a nonpositive sum. The negative baseline and signed tail provide
the estimate. -/
theorem quarter_gamma_phase_negative {y : ℝ} (hy : 12 ≤ y + 21 / 8)
    (hG :
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            target028GammaPhase y t)) :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            target028GammaPhase y t) +
        (∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2)) ≤
      0 := by
  have h := quarter_gamma_phase_baseline hy hG
  have hm := target028_gamma_phase_mass_nonneg y
  have hn : -(4 / 3 : ℝ) * (∫ t : ℝ, target028GammaPhase y t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hm
  exact h.trans hn

/-- For an even character at shifted scale at least twelve, the central Gamma
integral and first-pole resolvent retain the negative baseline times the density.
This transfers the signed phase estimate through the central-line representation. -/
theorem quarter_gamma_central_baseline {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hy : 12 ≤ Real.log x + 21 / 8) :
    (refinedCentralGammaPair χ x).re +
        (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) ≤
      -(4 / 3 : ℝ) * quarterGammaDensity (Real.log x + 21 / 8) := by
  let P := target028GammaPhase (Real.log x)
  let F : ℝ → ℂ := fun t ↦
    refinedReflectedGammaIntegrand χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
      refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ refinedReflectedGammaIntegrand χ⁻¹ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [refinedReflectedGammaIntegrand, mul_comm Complex.I, Complex.ofReal_zero] using
      (refined_reflected_gamma_line_integrable χ⁻¹ (c := 0) hx (by norm_num only) (by norm_num only)
        (by norm_num only))
  have hi2 :
    MeasureTheory.Integrable (fun t : ℝ ↦ refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [refinedGammaIntegrand, mul_comm Complex.I, Complex.ofReal_zero] using
      (refined_gamma_line_integrable χ (c := 0) hx (by norm_num only) (by norm_num only))
  have hFi : MeasureTheory.Integrable F := hi1.add hi2
  have hp (t : ℝ) : (x : ℂ) ^ (Complex.I * t) = Complex.exp (Complex.I * (t : ℂ) * Real.log x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hpoint (t : ℝ) :
    (F t).re =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t := by
    dsimp only [F, P, target028GammaPhase]
    rw [refined_even_gamma_integrand_eq χ he x t, hp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hG :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
          P t) := by
    exact hFi.re.congr (Filter.Eventually.of_forall hpoint)
  have hb := quarter_gamma_phase_baseline hy hG
  have hr := Complex.reCLM.integral_comp_comm hFi
  change (∫ t : ℝ, (F t).re) = (∫ t : ℝ, F t).re at hr
  have hint :
    (∫ t : ℝ, (F t).re) =
      ∫ t : ℝ,
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hpair :
    (refinedCentralGammaPair χ x).re =
      (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) /
        (2 * Real.pi) := by
    rw [← refined_central_gamma_pair_eq χ he hx, ← mul_add, ← MeasureTheory.integral_add hi1 hi2]
    change ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr, hint]
    ring
  have hd : 0 ≤ 2 * Real.pi := mul_nonneg (by norm_num only) Real.pi_pos.le
  have h := div_le_div_of_nonneg_right hb hd
  rw [add_div, ← hpair] at h
  have hm := quarter_phase_mass_eq_density (Real.log x)
  have he :
    (-(4 / 3 : ℝ) * (∫ t : ℝ, target028GammaPhase (Real.log x) t)) / (2 * Real.pi) =
      -(4 / 3 : ℝ) * quarterGammaDensity (Real.log x + 21 / 8) := by
    rw [← hm]
    ring
  rw [he] at h
  exact h

/-- For an even character at shifted scale at least twelve, the central Gamma
integral plus its first-pole resolvent is nonpositive. -/
theorem quarter_gamma_central_negative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hy : 12 ≤ Real.log x + 21 / 8) :
    (refinedCentralGammaPair χ x).re +
        (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) ≤
      0 := by
  have h := quarter_gamma_central_baseline χ he hx hy
  have hm : 0 ≤ quarterGammaDensity (Real.log x + 21 / 8) := by
    rw [← quarter_phase_mass_eq_density]
    exact mul_nonneg (by positivity) (target028_gamma_phase_mass_nonneg _)
  have hn : -(4 / 3 : ℝ) * quarterGammaDensity (Real.log x + 21 / 8) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hm
  exact h.trans hn

/-- For an even character, the first-pole correction and the negative baseline
are both retained in the central Gamma estimate above shifted scale twelve. -/
theorem quarter_gamma_first_baseline {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hy : 12 ≤ Real.log x + 21 / 8) :
    (refinedCentralGammaPair χ x).re + quarterGammaFirstCorrection (Real.log x + 21 / 8) ≤
      -(4 / 3 : ℝ) * quarterGammaDensity (Real.log x + 21 / 8) := by
  have h := quarter_gamma_central_baseline χ he hx hy
  have hy0 : 0 ≤ Real.log x + 21 / 8 := by linarith only [hy]
  have hl := quarter_first_phase_resolvent hy0
  change
    quarterGammaFirstCorrection (Real.log x + 21 / 8) ≤
      (1 / (2 * Real.pi)) * ∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2) at hl
  have hh :
    (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) =
      (1 / (2 * Real.pi)) * ∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2) := by
    ring
  rw [hh] at h
  linarith only [h, hl]

/-- For an even character at shifted scale at least twelve, the central Gamma
term and explicit first-pole correction have a nonpositive sum. -/
theorem quarter_gamma_first_negative {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hy : 12 ≤ Real.log x + 21 / 8) :
    (refinedCentralGammaPair χ x).re + quarterGammaFirstCorrection (Real.log x + 21 / 8) ≤ 0 := by
  have h := quarter_gamma_first_baseline χ he hx hy
  have hm : 0 ≤ quarterGammaDensity (Real.log x + 21 / 8) := by
    rw [← quarter_phase_mass_eq_density]
    exact mul_nonneg (by positivity) (target028_gamma_phase_mass_nonneg _)
  have hn : -(4 / 3 : ℝ) * quarterGammaDensity (Real.log x + 21 / 8) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hm
  exact h.trans hn

end PseudoPrime.PrimeTestBounds.MillerRabin
