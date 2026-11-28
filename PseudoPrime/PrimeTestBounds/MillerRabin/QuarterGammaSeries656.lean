/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma644
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaDerivative
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaBaseline
import PseudoPrime.LLS.PaperStatements.GammaScalarArchimedeanBounds
import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaRationalCertificate
import PseudoPrime.Analysis.ExponentialFourierProduct
public import PseudoPrime.Analysis.ExponentialMomentTail
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution

/-! # Pole decomposition for the section 132 central Gamma integral -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Fourier transform of the sixth-pole kernel is its inverse Mellin
profile at `exp (-y)`, with the exact Fourier normalization. This identity
also supplies the profile inside the scaled resolvent convolution. -/
theorem quarter_main_fourier_656 (y : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) =
      (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-y)) : ℂ) := by
  have hu : 0 < Real.exp (-y) := Real.exp_pos _
  have hinv := quarter_main_inversion_656 (σ := 0) (u := Real.exp (-y)) (by norm_num only) hu
  have hphase (t : ℝ) :
    (Real.exp (-y) : ℂ) ^ (-(Complex.I * t)) = Complex.exp (Complex.I * (t : ℂ) * y) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le]
    rw [Real.log_exp, Complex.ofReal_neg]
    congr 1
    ring
  unfold Analysis.inverseMellin at hinv
  simpa only [Complex.ofReal_zero, zero_add, hphase] using hinv

/-- The sixth-pole kernel is continuous on the imaginary axis, which stays
strictly to the right of its unique pole. This permits the product Fubini
estimate to be applied to the actual Gamma kernel. -/
theorem quarter_main_line_cont_656 :
    Continuous (fun t : ℝ ↦ quarterKernel656.function (Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hden : Complex.I * (t : ℂ) + 11 / 10 ≠ 0 := by
    intro h
    have h27 : (11 / 10 : ℂ) = (((11 / 10 : ℝ)) : ℂ) := by
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [h27] at h
    have hr := congrArg Complex.re h
    norm_num only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.zero_re] at hr
  have he :
    (fun t : ℝ ↦ quarterKernel656.function (Complex.I * t)) = fun t : ℝ ↦
      ((11 / 10 : ℂ) ^ 5) *
        (Complex.exp ((21 / 8 : ℂ) * (Complex.I * t)) / (Complex.I * t + 11 / 10) ^ 6) := by
    funext t
    simpa only [mul_div_assoc] using quarter_function_656 (Complex.I * t)
  rw [he]
  fun_prop (disch := exact pow_ne_zero 6 hden)

/-- The sixth-pole kernel multiplied by a real Fourier phase remains
continuous and integrable. The phase has unit norm, so the Mellin-kernel
integrability estimate applies at every shift. -/
theorem quarter_main_phase_regular_656 (y : ℝ) :
    Continuous
        (fun t : ℝ ↦
          quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  constructor
  · exact quarter_main_line_cont_656.mul hp
  · have hk :=
      LLS.PaperStatements.MellinKernel.integrable_line quarterKernel656 (c := 0) (by norm_num only)
        (by linarith only [quarterKernel656.delta_pos])
    have hk' :
      MeasureTheory.Integrable (fun t : ℝ ↦ quarterKernel656.function (Complex.I * t)) := by
      simpa only [Complex.ofReal_zero, zero_add] using hk
    apply hk'.mul_bdd (c := 1) hp.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero]

/-- Real oscillatory factor of the section 132 kernel at logarithmic scale y. -/
noncomputable def gammaPhase656 (y t : ℝ) : ℝ :=
  (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)).re

/-- For an even character, the sum of the reflected and right central
Gamma integrands equals the real digamma factor times the complex kernel phase. -/
theorem even_gamma_integrand_eq_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (x t : ℝ) :
    reflectedGammaIntegrand656 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
        gammaIntegrand656 χ x ((0 : ℂ) + t * Complex.I) =
      (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi : ℝ) :
          ℂ) *
        (quarterKernel656.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
  have hs : star (Complex.I * (t : ℂ) + 1 / 2) = 1 / 2 - Complex.I * t := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
      map_one, map_ofNat]
    ring
  have hd := refined_even_gamma_real_digamma χ he t
  unfold reflectedGammaIntegrand656 gammaIntegrand656
  simp only [zero_add, mul_comm (t : ℂ) Complex.I, hγ]
  rw [← hs, refined_even_gamma_logDeriv_conj χ he, ← hd]
  have heq :
    star (logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2)) +
        logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2) =
      (((2 : ℝ) * (logDeriv χ.gammaFactor (Complex.I * (t : ℂ) + 1 / 2)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]
      ring
    · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im]
      ring
  rw [← heq]
  ring

/-- For an even character and positive x, the real central integral is the
normalized integral of the real digamma weight against the section 132 phase.
Absolute integrability permits commuting the real part with the integral. -/
theorem central_real_phase_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even) {x : ℝ}
    (hx : 0 < x) :
    let f := fun t : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
        gammaPhase656 (Real.log x) t
    MeasureTheory.Integrable f ∧ (centralGammaPair656 χ x).re = (∫ t : ℝ, f t) / (2 * Real.pi) := by
  let P := gammaPhase656 (Real.log x)
  let F : ℝ → ℂ := fun t ↦
    reflectedGammaIntegrand656 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
      gammaIntegrand656 χ x ((0 : ℂ) + t * Complex.I)
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand656 χ⁻¹ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand656, mul_comm Complex.I, Complex.ofReal_zero] using
      (reflected_gamma_line_integrable_656 χ⁻¹ (c := 0) hx (by norm_num only) (by norm_num only)
        (by norm_num only))
  have hi2 :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaIntegrand656 χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [gammaIntegrand656, mul_comm Complex.I, Complex.ofReal_zero] using
      (gamma_line_integrable_656 χ (c := 0) hx (by norm_num only) (by norm_num only))
  have hFi : MeasureTheory.Integrable F := hi1.add hi2
  have hp (t : ℝ) : (x : ℂ) ^ (Complex.I * t) = Complex.exp (Complex.I * (t : ℂ) * Real.log x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hpoint (t : ℝ) :
    (F t).re =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t := by
    dsimp only [F, P, gammaPhase656]
    rw [even_gamma_integrand_eq_656 χ he x t, hp]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hG :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
          P t) := by
    exact hFi.re.congr (Filter.Eventually.of_forall hpoint)
  have hr := Complex.reCLM.integral_comp_comm hFi
  change (∫ t : ℝ, (F t).re) = (∫ t : ℝ, F t).re at hr
  have hint :
    (∫ t : ℝ, (F t).re) =
      ∫ t : ℝ,
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)
  have hpair :
    (centralGammaPair656 χ x).re =
      (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) /
        (2 * Real.pi) := by
    rw [← central_gamma_pair_eq_656 χ he hx, ← mul_add, ← MeasureTheory.integral_add hi1 hi2]
    change ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr, hint]
    ring
  exact ⟨hG, hpair⟩

/-- The real phase associated with the main kernel is continuous and integrable. -/
theorem gamma_phase_integrable_656 (y : ℝ) :
    Continuous (gammaPhase656 y) ∧ MeasureTheory.Integrable (gammaPhase656 y) := by
  exact
    ⟨Complex.continuous_re.comp (quarter_main_phase_regular_656 y).1,
      (quarter_main_phase_regular_656 y).2.re⟩

/-- The second height moment of the sixth-pole kernel is integrable. Scale
the difference of the integrable second and third Cauchy powers. -/
theorem second_integrable_656 :
    MeasureTheory.Integrable (fun t : ℝ ↦ t ^ 2 * ‖quarterKernel656.function (Complex.I * t)‖) := by
  have h2 := Analysis.integrable_cauchy_power (by norm_num only : 1 ≤ 2)
  have h3 := Analysis.integrable_cauchy_power (by norm_num only : 1 ≤ 3)
  have hn : MeasureTheory.Integrable (fun t : ℝ ↦ t ^ 2 / (1 + t ^ 2) ^ 3) := by
    apply (h2.sub h3).congr
    apply Filter.Eventually.of_forall
    intro t
    have h : 1 + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg t])
    dsimp only [Pi.sub_apply]
    field_simp
    ring
  have hi :=
    ((MeasureTheory.integrable_comp_mul_left_iff (fun t : ℝ ↦ t ^ 2 / (1 + t ^ 2) ^ 3)
              (by norm_num only : (10 / 11 : ℝ) ≠ 0)).mpr
          hn).const_mul
      (11 / 10 : ℝ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [quarter_zero_norm_656]
  have h1 : (11 / 10 : ℝ) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h2 : 1 + ((10 / 11 : ℝ) * t) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The term after the first pole in the even digamma correction, multiplied by the
real oscillatory phase. Its index starts at the pole with rate `5/2`. -/
noncomputable def gammaTailTerm656 (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((t / 2) ^ 2 / ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2))) *
    gammaPhase656 y t

/-- Each signed tail term is absolutely bounded by the second kernel moment times
the corresponding inverse cube. This is the majorant for termwise integration. -/
theorem gamma_tail_term_bound_656 (y : ℝ) (n : ℕ) (t : ℝ) :
    ‖gammaTailTerm656 y n t‖ ≤
      (2 / (2 * (n : ℝ) + 5 / 2) ^ 3) * (t ^ 2 * ‖quarterKernel656.function (Complex.I * t)‖) := by
  have ha : 0 < (1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ) := by positivity
  have hd :
    0 ≤
      (t / 2) ^ 2 /
        ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg ha.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hp : |gammaPhase656 y t| ≤ ‖quarterKernel656.function (Complex.I * t)‖ := by
    have h :=
      Complex.abs_re_le_norm
        (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y))
    rw [norm_mul, Complex.norm_exp] at h
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero, mul_one] at h
    exact h
  rw [gammaTailTerm656, norm_mul, Real.norm_eq_abs, abs_of_nonneg hd, Real.norm_eq_abs]
  have h :=
    mul_le_mul (target028_gamma_correction_term t n) hp (abs_nonneg _)
      (le_trans hd (target028_gamma_correction_term t n))
  convert h using 1
  ring

/-- Each tail term is integrable: its continuous integrand is dominated by the
integrable second moment of the sixth-pole kernel. -/
theorem gamma_tail_term_integrable_656 (y : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (gammaTailTerm656 y n) := by
  have hd (t : ℝ) :
    (1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2) ≠ 0 := by
    positivity
  have hc : Continuous (gammaTailTerm656 y n) := by
    unfold gammaTailTerm656
    apply Continuous.mul
    · exact
        ((continuous_id.div_const 2).pow 2).div
          (continuous_const.mul (continuous_const.add ((continuous_id.div_const 2).pow 2))) hd
    · exact (gamma_phase_integrable_656 y).1
  apply
    (second_integrable_656.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (gamma_tail_term_bound_656 y n)

/-- The integrals of the absolute tail terms form a convergent series, using the
summable inverse-cube bound for the pole rates. -/
theorem gamma_tail_norm_summable_656 (y : ℝ) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖gammaTailTerm656 y n t‖) := by
  let C : ℝ := ∫ t : ℝ, t ^ 2 * ‖quarterKernel656.function (Complex.I * t)‖
  have hs : Summable (fun n : ℕ ↦ (2 * C) * (1 / (2 * (n : ℝ) + 5 / 2) ^ 3)) :=
    target028_gamma_pole_tail_summable.mul_left (2 * C)
  apply hs.of_nonneg_of_le
  · intro n
    exact MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _)
  · intro n
    have hi := gamma_tail_term_integrable_656 y n
    have hmajor := second_integrable_656.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)
    have h := MeasureTheory.integral_mono hi.norm hmajor (gamma_tail_term_bound_656 y n)
    rw [MeasureTheory.integral_const_mul] at h
    dsimp only [C]
    convert h using 1
    ring

/-- The oscillatory even-Gamma tail can be integrated term by term: the individual
terms are integrable and their integral norms form a summable series. -/
theorem gamma_tail_integral_tsum_656 (y : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, gammaTailTerm656 y n t) = ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm656 y n t := by
  exact
    (MeasureTheory.integral_tsum_of_summable_integral_norm (gamma_tail_term_integrable_656 y)
        (gamma_tail_norm_summable_656 y)).symm

/-- The oscillatory digamma increment after removing its first pole equals the
convergent series of signed tail terms. The identity separates the first term of
the vertical digamma expansion and distributes the phase over the remaining sum. -/
theorem gamma_tail_eq_series_656 (y t : ℝ) :
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        gammaPhase656 y t =
      ∑' n : ℕ, gammaTailTerm656 y n t := by
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
  simp only [gammaTailTerm656, tsum_mul_right]
  have he := congrArg (fun x : ℝ ↦ (x - (4 - 1 / (1 / 4 + t ^ 2))) * gammaPhase656 y t) h
  simpa only [add_sub_cancel_left, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using he

/-- The actual phase divided by the first-pole denominator is integrable.
The reciprocal denominator is continuous and bounded by four. -/
theorem resolvent_integrable_656 (y : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase656 y t / (1 / 4 + t ^ 2)) := by
  have hden (t : ℝ) : 1 / 4 + t ^ 2 ≠ (0 : ℝ) := by nlinarith only [sq_nonneg t]
  have hc : Continuous (fun t : ℝ ↦ (1 / 4 + t ^ 2)⁻¹) := by
    exact (continuous_const.add (continuous_id.pow 2)).inv₀ hden
  have hi := (gamma_phase_integrable_656 y).2
  have hm := hi.mul_bdd (c := 4) hc.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(1 / 4 + t ^ 2)⁻¹‖ ≤ (4 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs,
      abs_of_nonneg
        (inv_nonneg.mpr
          (le_of_lt (lt_of_le_of_ne (by nlinarith only [sq_nonneg t]) (Ne.symm (hden t)))))]
    rw [← one_div]
    apply (div_le_iff₀ (by nlinarith only [sq_nonneg t])).2
    nlinarith only [sq_nonneg t]
  simpa only [div_eq_mul_inv] using hm hb

/-- The real even-Gamma integral is its baseline mass minus the first
resolvent, plus the sum of the remaining pole integrals. -/
theorem quarter_gamma_first_split_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    let y := Real.log x
    let P := gammaPhase656 y
    let B := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4
    (centralGammaPair656 χ x).re =
      (1 / (2 * Real.pi)) *
        (B * (∫ t : ℝ, P t) - (∫ t : ℝ, P t / (1 / 4 + t ^ 2)) +
          ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm656 y n t) := by
  intro y P B
  obtain ⟨hG, hcentral⟩ := central_real_phase_656 χ he hx
  let G := fun t : ℝ ↦
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t
  let R := fun t : ℝ ↦ P t / (1 / 4 + t ^ 2)
  have hP := (gamma_phase_integrable_656 y).2
  have hR := resolvent_integrable_656 y
  have hsum : (∫ t : ℝ, G t - B * P t + R t) = ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm656 y n t := by
    rw [← gamma_tail_integral_tsum_656 y]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [← gamma_tail_eq_series_656 y t]
    dsimp only [G, R, B, P]
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hGi : MeasureTheory.Integrable G := hG
  have hRi : MeasureTheory.Integrable R := hR
  have hPi : MeasureTheory.Integrable P := hP
  have hadd := MeasureTheory.integral_add (hGi.sub (hPi.const_mul B)) hRi
  have hsub := MeasureTheory.integral_sub hGi (hPi.const_mul B)
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, MeasureTheory.integral_const_mul] at hsum
  have h₁ : (centralGammaPair656 χ x).re = (∫ t : ℝ, G t) / (2 * Real.pi) := hcentral
  rw [h₁, ← hsum]
  ring

/-- For a positive pole rate, the real phase resolvent is the real part of the
complex resolvent integral. The reciprocal denominator is bounded by `1 / c²`. -/
theorem phase_resolvent_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, gammaPhase656 y t / (c ^ 2 + t ^ 2)) =
      (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hcont : Continuous (fun t : ℝ ↦ (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t ↦ (hden t).ne'))
  have hi := (quarter_main_phase_regular_656 y).2
  have hm := hi.mul_bdd (c := (c ^ 2)⁻¹) hcont.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (c ^ 2)⁻¹ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hden t).le)]
    exact inv_anti₀ (sq_pos_of_pos hc) (le_add_of_nonneg_right (sq_nonneg t))
  have hr := Complex.reCLM.integral_comp_comm (hm hb)
  change
    (∫ t : ℝ,
        (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) =
      _ at hr
  have he :
    (∫ t : ℝ, gammaPhase656 y t / (c ^ 2 + t ^ 2)) =
      ∫ t : ℝ,
        (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [gammaPhase656, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  rw [he, hr]
  simp only [one_div]
  rfl

/-- In the two broad comparisons the level-one Gamma term is the
baseline integral minus the first resolvent plus the convergent tail. -/
theorem quarter_level_gamma_split_656 {x : ℝ} (hx : 1 ≤ x) :
    let y := Real.log x
    let P := gammaPhase656 y
    let B := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4
    (quarterLevelGamma656 x).re =
      (1 / (2 * Real.pi)) *
        (B * (∫ t : ℝ, P t) - (∫ t : ℝ, P t / (1 / 4 + t ^ 2)) +
          ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm656 y n t) := by
  rw [quarter_level_gamma_central_656 hx]
  exact
    quarter_gamma_first_split_656 (1 : DirichletCharacter ℂ 1)
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even (zero_lt_one.trans_le hx)

/-- The normalized resolvent integral of the shifted sixth-pole kernel is the
exponential convolution of its inverse Mellin profile. This exact identity
holds at every real resolvent scale and is the starting point for estimating
individual terms of the even-Gamma expansion. -/
theorem quarter_main_resolvent_656 (y s : ℝ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + ((s * t : ℝ) : ℂ) ^ 2))) =
      ∫ v : ℝ,
        (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-(y + s * v))) : ℂ) *
          (Analysis.ExponentialMeanSquare.weight v : ℂ) := by
  let F : ℝ → ℂ := fun t ↦
    quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)
  have hf : Continuous F := (quarter_main_phase_regular_656 y).1
  have hi : MeasureTheory.Integrable F := (quarter_main_phase_regular_656 y).2
  rw [Analysis.exponential_fourier_resolvent_convolution F hf hi s, ←
    MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  have he :
    (∫ t : ℝ, F t * Complex.exp (Complex.I * (s * (t : ℂ)) * v)) =
      ∫ t : ℝ,
        quarterKernel656.function (Complex.I * t) *
          Complex.exp (Complex.I * (t : ℂ) * (y + s * v : ℝ)) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only [F]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    simp only [Complex.ofReal_add, Complex.ofReal_mul]
    ring
  rw [← mul_assoc, he, quarter_main_fourier_656]

/-- For a positive pole parameter, rescale the sixth-pole convolution so
that its exponential kernel has decay rate `c`. The prefactor is the exact
Jacobian `c / 2`. -/
theorem quarter_main_resolvent_pole_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2))) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  rw [quarter_main_resolvent_656 y (2 / c)]
  let g : ℝ → ℂ := fun w ↦
    (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-(y + w))) : ℂ)
  have hs : 0 < 2 / c := div_pos (by norm_num only) hc
  have h := Analysis.exponential_convolution_rescale g hs
  have he : 2 / (2 / c) = c := by
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ c (by norm_num only : (2 : ℝ) ≠ 0)]
  have hi : (2 / c)⁻¹ = c / 2 := by rw [inv_div]
  simpa only [g, he, ← Complex.ofReal_inv, hi] using h

/-- The usual resolvent at a positive pole has the same profile convolution
after multiplying its Fourier integral by `c²`. This exact form keeps the
normalization explicit for the even-Gamma partial fractions. -/
theorem quarter_main_pole_conv_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ w : ℝ,
          (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-(y + w))) : ℂ) *
            (Real.exp (-c * |w|) : ℂ) := by
  have h := quarter_main_resolvent_pole_656 y hc
  have he :
    ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ∫ t : ℝ,
        (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
          ((4 : ℂ) / (4 + (((2 / c) * t : ℝ) : ℂ) ^ 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    have hh := congrArg Complex.ofReal (quarter_scaled_resolvent (t := t) hc)
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one] at hh ⊢
    rw [hh]
    ring
  rw [mul_assoc, he]
  exact h

/-- Translate the profile convolution to the profile variable. The
exponential kernel is then centered at `y`, the form used to analyze its
individual Gamma poles. -/
theorem quarter_main_pole_centered_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ,
          (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-v)) : ℂ) *
            (Real.exp (-c * |v - y|) : ℂ) := by
  rw [quarter_main_pole_conv_656 y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦
    (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-v)) : ℂ) *
      (Real.exp (-c * |v - y|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f y
  simpa only [f, add_sub_cancel_left] using h

/-- The sixth-pole inverse Mellin profile in its shifted logarithmic
variable. It vanishes for negative arguments and equals the exponential fifth
moment on the positive half-line, including the kernel normalization. -/
noncomputable def quarterGammaDensity656 (v : ℝ) : ℝ :=
  if 0 ≤ v then ((11 / 10 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(11 / 10 : ℝ) * v) else 0

/-- The inverse Mellin profile at `exp (21/8 - v)` is the shifted density.
The support condition is exactly `0 ≤ v`; on that support the rational pole
formula reduces to an exponential fifth moment. -/
theorem quarter_profile_shift_656 (v : ℝ) :
    Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (21 / 8 - v)) =
      quarterGammaDensity656 v := by
  unfold Analysis.rationalPoleProfile quarterGammaDensity656
  rw [Real.log_exp]
  by_cases hv : 0 ≤ v
  · rw [ite_eq_left ⟨Real.exp_pos _, by linarith only [hv]⟩, ite_eq_left hv]
    norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
    have he : -(((21 / 8 : ℝ) - (21 / 8 - v)) / (10 / 11)) = -(11 / 10 : ℝ) * v := by ring
    rw [he]
    ring
  · rw [ite_eq_right
        (by
          intro h; apply hv; linarith only [h.2]),
      ite_eq_right hv]

/-- The positive-pole resolvent is the convolution of the shifted density
with `exp (-c |v - z|)`, where `z = y + 21/8`. This rewrites the exact
Fourier identity in the logarithmic variables used for the Gamma-tail bound. -/
theorem quarter_pole_density_conv_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ, (quarterGammaDensity656 v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ) := by
  rw [quarter_main_pole_centered_656 y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦ (quarterGammaDensity656 v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f (21 / 8 : ℝ)
  calc
    _ = ∫ u : ℝ, f (21 / 8 + u) := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only [f]
      have hu : (21 / 8 : ℝ) - (21 / 8 + u) = -u := by ring
      have harg : (21 / 8 : ℝ) + u - (y + 21 / 8) = u - y := by ring
      rw [← hu, quarter_profile_shift_656, harg]
    _ = _ := h

/-- The shifted density vanishes on the nonpositive half-line. Hence the
pole convolution may be restricted to the positive half-line, including at
the boundary where its fifth power is zero. -/
theorem quarter_pole_density_pos_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v in Set.Ioi (0 : ℝ),
          (quarterGammaDensity656 v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ) := by
  rw [quarter_pole_density_conv_656 y hc]
  congr 1
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (show v ∈ Set.Ioi (0 : ℝ) from hv)]
  · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0 : ℝ) from hv)]
    have hv0 : v ≤ 0 := le_of_not_gt hv
    have hd : quarterGammaDensity656 v = 0 := by
      by_cases heq : v = 0
      · subst v
        norm_num only [quarterGammaDensity656, le_refl, ite_true, zero_pow, OfNat.ofNat_ne_zero,
          mul_zero, zero_mul]
      · rw [quarterGammaDensity656, ite_eq_right (not_le_of_gt (lt_of_le_of_ne hv0 heq))]
    rw [hd]
    norm_num only [Complex.ofReal_zero, zero_mul]

/-- The shifted profile convolved with an exponential of rate `c`, over
the profile's positive support. This is the individual pole contribution
used in the even-Gamma tail estimate. -/
noncomputable def quarterGammaConvolution656 (z c : ℝ) : ℝ :=
  ∫ v in Set.Ioi (0 : ℝ), quarterGammaDensity656 v * Real.exp (-c * |v - z|)

/-- The positive-support convolution is integrable for nonnegative decay
rate. Its kernel is bounded by one and the fifth exponential moment supplies
an integrable majorant. -/
theorem quarter_gamma_conv_integrable_656 (z : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ quarterGammaDensity656 v * Real.exp (-c * |v - z|))
      (Set.Ioi 0) := by
  have hi' :
    MeasureTheory.IntegrableOn (fun v : ℝ ↦ v ^ 5 * Real.exp (-(11 / 10 : ℝ) * v)) (Set.Ioi 0) :=
    Analysis.exponential_moment_integrable (by norm_num only) 5
  let f : ℝ → ℝ := fun v ↦
    ((11 / 10 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(11 / 10 : ℝ) * v) * Real.exp (-c * |v - z|)
  have hcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hmajor := hi'.const_mul ((11 / 10 : ℝ) ^ 5 / 120)
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    refine hmajor.mono' (hcont.continuousOn.aestronglyMeasurable measurableSet_Ioi) ?_
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
    intro v hv
    have hvpos : 0 < v := hv
    have hbase : 0 ≤ ((11 / 10 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(11 / 10 : ℝ) * v) := by
      positivity
    have he : Real.exp (-c * |v - z|) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (abs_nonneg _))
    dsimp only [f]
    rw [Real.norm_of_nonneg (mul_nonneg hbase (Real.exp_pos _).le)]
    simpa only [mul_assoc] using mul_le_of_le_one_right hbase he
  apply hf.congr_fun _ measurableSet_Ioi
  intro v hv
  dsimp only [f, quarterGammaDensity656]
  rw [ite_eq_left hv.le]

/-- The real part of the normalized positive-pole resolvent equals its
positive-half-line density convolution, with the exact factors of `c` and
`2π`. Integrability justifies moving the real embedding through the integral. -/
theorem quarter_gamma_pole_real_656 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (1 / (2 * Real.pi)) * c ^ 2 *
        (∫ t : ℝ,
            (quarterKernel656.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
              ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re =
      (c / 2) * quarterGammaConvolution656 (y + 21 / 8) c := by
  have h := quarter_pole_density_pos_656 y hc
  have hi := quarter_gamma_conv_integrable_656 (y + 21 / 8) hc.le
  have hcast := Complex.ofRealCLM.integral_comp_comm hi
  change
    (∫ v in Set.Ioi (0 : ℝ),
        ((quarterGammaDensity656 v * Real.exp (-c * |v - (y + 21 / 8)|) : ℝ) : ℂ)) =
      ((quarterGammaConvolution656 (y + 21 / 8) c : ℝ) : ℂ) at hcast
  simp only [Complex.ofReal_mul] at hcast
  rw [hcast] at h
  have hr := congrArg Complex.re h
  simpa only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, add_zero, sub_zero] using hr

/-- On the initial interval, the density and pole exponential combine into
one fifth exponential moment with rate `11/10 - c`. The scale-dependent
factor is constant and can be evaluated separately. -/
theorem quarter_gamma_initial_656 (z c : ℝ) :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity656 v * Real.exp (-c * (z - v))) =
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
        ∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((11 / 10 : ℝ) - c) * v) := by
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro v hv
  dsimp only
  rw [quarterGammaDensity656, ite_eq_left hv.1.le]
  have he : -(11 / 10 : ℝ) * v + -c * (z - v) = -c * z + -((11 / 10 : ℝ) - c) * v := by ring
  have hexp :
    Real.exp (-(11 / 10 : ℝ) * v) * Real.exp (-c * (z - v)) =
      Real.exp (-c * z) * Real.exp (-((11 / 10 : ℝ) - c) * v) := by
    rw [← Real.exp_add, he, Real.exp_add]
  have hm := congrArg (fun x : ℝ ↦ ((11 / 10 : ℝ) ^ 5 / 120) * v ^ 5 * x) hexp
  nlinarith only [hm]

/-- For nonnegative shift and pole parameter, split the Gamma convolution at the shift.
Absolute-value simplification gives the left and right exponential integrals. -/
theorem quarter_gamma_conv_split_656 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution656 z c =
      (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity656 v * Real.exp (-c * (z - v))) +
        ∫ v in Set.Ioi z, quarterGammaDensity656 v * Real.exp (-c * (v - z)) := by
  have hi := quarter_gamma_conv_integrable_656 z hc
  have hi1 := hi.mono_set (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) z ⊆ Set.Ioi 0)
  have hi2 := hi.mono_set (Set.Ioi_subset_Ioi hz)
  have he1 :
    (∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity656 v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioc (0 : ℝ) z, quarterGammaDensity656 v * Real.exp (-c * (z - v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro v hv
    dsimp only
    rw [abs_of_nonpos (sub_nonpos.mpr hv.2), neg_sub]
  have he2 :
    (∫ v in Set.Ioi z, quarterGammaDensity656 v * Real.exp (-c * |v - z|)) =
      ∫ v in Set.Ioi z, quarterGammaDensity656 v * Real.exp (-c * (v - z)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hv.le)]
  unfold quarterGammaConvolution656
  rw [← Set.Ioc_union_Ioi_eq_Ioi hz,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hi1 hi2, he1, he2]

/-- For nonnegative shift and pole rate, the upper half of the convolution is the
closed fifth exponential tail. This supplies the right contribution in the pole estimate. -/
theorem quarter_gamma_right_moment_656 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    (∫ v in Set.Ioi z, quarterGammaDensity656 v * Real.exp (-c * (v - z))) =
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-(11 / 10 : ℝ) * z)) *
        Analysis.logPowerTailPoly (c + 11 / 10) 5 z := by
  have hr : 0 < c + (11 / 10 : ℝ) := by linarith only [hc]
  have he :
    (∫ v in Set.Ioi z, quarterGammaDensity656 v * Real.exp (-c * (v - z))) =
      ∫ v in Set.Ioi z,
        (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (c * z)) *
          (v ^ 5 * Real.exp (-(c + 11 / 10) * v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    dsimp only
    rw [quarterGammaDensity656, ite_eq_left (hz.trans hv.le)]
    rw [mul_assoc _ (Real.exp _) (Real.exp _), ← Real.exp_add]
    have hexp : -(11 / 10 : ℝ) * v + -c * (v - z) = c * z + -(c + 11 / 10) * v := by ring
    rw [hexp, Real.exp_add]
    ring
  rw [he, MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail hr hz 5]
  rw [mul_assoc ((11 / 10 : ℝ) ^ 5 / 120), ← mul_assoc (Real.exp _) (Real.exp _), ← Real.exp_add]
  have hexp : c * z + -(c + 11 / 10) * z = -(11 / 10 : ℝ) * z := by ring
  rw [hexp, mul_assoc]

/-- For a nonnegative shift and pole rate, express the Gamma convolution as an initial
moment plus its closed upper tail. This prepares the higher-pole comparison. -/
theorem quarter_gamma_conv_moments_656 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c) :
    quarterGammaConvolution656 z c =
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-((11 / 10 : ℝ) - c) * v)) +
        (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-(11 / 10 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 11 / 10) 5 z := by
  rw [quarter_gamma_conv_split_656 hz hc, quarter_gamma_initial_656,
    quarter_gamma_right_moment_656 hz hc]

/-- For a nonnegative shift and nonnegative pole rate different from the profile rate,
evaluate both halves of the Gamma convolution in closed form. -/
theorem quarter_gamma_conv_closed_656 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (11 / 10 : ℝ)) :
    quarterGammaConvolution656 z c =
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          (Analysis.logPowerTailPoly (11 / 10 - c) 5 0 -
            Real.exp (-((11 / 10 : ℝ) - c) * z) * Analysis.logPowerTailPoly (11 / 10 - c) 5 z) +
        (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-(11 / 10 : ℝ) * z)) *
          Analysis.logPowerTailPoly (c + 11 / 10) 5 z := by
  have hr : (11 / 10 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  rw [quarter_gamma_conv_moments_656 hz hc, Analysis.exponential_moment_interval_ne hr hz 5]

/-- For every later Gamma pole, separate the closed convolution into its polynomial
part and the positive exponential endpoint term. -/
theorem quarter_gamma_conv_expansion_656 {z c : ℝ} (hz : 0 ≤ z) (hc : 0 ≤ c)
    (hne : c ≠ (11 / 10 : ℝ)) :
    quarterGammaConvolution656 z c =
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-(11 / 10 : ℝ) * z)) *
          (Analysis.logPowerTailPoly (c + 11 / 10) 5 z -
            Analysis.logPowerTailPoly (11 / 10 - c) 5 z) +
        (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-c * z)) *
          Analysis.logPowerTailPoly (11 / 10 - c) 5 0 := by
  rw [quarter_gamma_conv_closed_656 hz hc hne]
  have hexp :
    Real.exp (-c * z) * Real.exp (-((11 / 10 : ℝ) - c) * z) = Real.exp (-(11 / 10 : ℝ) * z) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  ring

/-- The part of the first Gamma pole supported below the shifted cutoff.
The decay rate in its fifth moment is 3/5. -/
noncomputable def quarterGammaFirst656 (z : ℝ) : ℝ :=
  ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(1 / 2) * z)) *
    ∫ v in Set.Ioc (0 : ℝ) z, v ^ 5 * Real.exp (-(3 / 5) * v)

/-- The first resolvent splits at the shifted logarithmic cutoff into
the truncated fifth moment and the explicit forward polynomial. -/
theorem quarter_first_conv_split_656 {z : ℝ} (hz : 0 ≤ z) :
    quarterGammaConvolution656 z (1 / 2) =
      quarterGammaFirst656 z +
        ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z)) *
          Analysis.logPowerTailPoly (8 / 5) 5 z := by
  rw [quarter_gamma_conv_moments_656 hz (by norm_num only), quarterGammaFirst656]
  norm_num only

/-- The first-pole term in the level-one split is exactly the truncated
moment plus the forward polynomial at the shifted logarithmic scale. -/
theorem quarter_first_resolvent_eq_656 {y : ℝ} (hy : 0 ≤ y + 21 / 8) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaPhase656 y t / (1 / 4 + t ^ 2)) =
      quarterGammaFirst656 (y + 21 / 8) +
        ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * (y + 21 / 8))) *
          Analysis.logPowerTailPoly (8 / 5) 5 (y + 21 / 8) := by
  have h := quarter_gamma_pole_real_656 y (c := 1 / 2) (by norm_num only)
  have hr := phase_resolvent_656 y (c := 1 / 2) (by norm_num only)
  norm_num only at h hr
  rw [← hr, quarter_first_conv_split_656 hy] at h
  linarith only [h]

/-- The odd-order digamma coefficient is a factorial multiple of the
difference of reciprocal-power series at the two gamma arguments. -/
noncomputable def quarterGammaOdd656 (j : ℕ) : ℝ :=
  (j.factorial : ℝ) / 2 ^ (j + 1) *
    ((∑' n : ℕ, (7 / 10 + n : ℝ) ^ (-((j : ℝ) + 1))) - ∑' n : ℕ, (4 / 5 + n : ℝ) ^ (-((j : ℝ) + 1)))

/-- Each complementary pole integral is the normalized density contribution
minus the corresponding positive-support convolution. -/
theorem quarter_gamma_tail_conv_656 (y : ℝ) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 21 / 8
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm656 y n t) =
      (2 / c) * quarterGammaDensity656 z - quarterGammaConvolution656 z c := by
  let c : ℝ := 2 * (n : ℝ) + 5 / 2
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hc0 : 0 < c := by linarith only [hc]
  have hden (t : ℝ) : c ^ 2 + t ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (sq_nonneg t)).ne'
  have he (t : ℝ) :
    gammaTailTerm656 y n t =
      (2 / c) * (gammaPhase656 y t - c ^ 2 * (gammaPhase656 y t / (c ^ 2 + t ^ 2))) := by
    dsimp only [gammaTailTerm656, c]
    push_cast
    field_simp
    ring
  have hr (t : ℝ) :
    gammaPhase656 y t / (c ^ 2 + t ^ 2) =
      (c ^ 2)⁻¹ * (gammaPhase656 y t - (c / 2) * gammaTailTerm656 y n t) := by
    rw [he]
    field_simp
    ring
  have hiP := (gamma_phase_integrable_656 y).2
  have hiF := gamma_tail_term_integrable_656 y n
  have hiR : MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase656 y t / (c ^ 2 + t ^ 2)) := by
    apply ((hiP.sub (hiF.const_mul (c / 2))).const_mul (c ^ 2)⁻¹).congr
    exact Filter.Eventually.of_forall (fun t ↦ (hr t).symm)
  have hint :
    (∫ t : ℝ, gammaTailTerm656 y n t) =
      (2 / c) *
        ((∫ t : ℝ, gammaPhase656 y t) - c ^ 2 * ∫ t : ℝ, gammaPhase656 y t / (c ^ 2 + t ^ 2)) := by
    have hfun :
      gammaTailTerm656 y n = fun t ↦
        (2 / c) * (gammaPhase656 y t - c ^ 2 * (gammaPhase656 y t / (c ^ 2 + t ^ 2))) :=
      funext he
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hiP (hiR.const_mul _),
      MeasureTheory.integral_const_mul]
  have hmass := congrArg Complex.re (quarter_main_fourier_656 y)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hmass
  have hre := Complex.reCLM.integral_comp_comm (quarter_main_phase_regular_656 y).2
  change
    (∫ t : ℝ, gammaPhase656 y t) =
      (∫ t : ℝ,
          quarterKernel656.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hre
  rw [← hre] at hmass
  change
    1 / (2 * Real.pi) * (∫ t : ℝ, gammaPhase656 y t) =
      Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (Real.exp (-y)) at hmass
  have harg : (21 / 8 : ℝ) - (y + 21 / 8) = -y := by ring
  rw [← harg, quarter_profile_shift_656] at hmass
  have hconv := quarter_gamma_pole_real_656 y hc0
  rw [← phase_resolvent_656 y hc0] at hconv
  dsimp only
  change _ = (2 / c) * _ - _
  rw [hint]
  have hc' : (5 / 2 : ℝ) + (n : ℝ) * 2 = c := by
    dsimp only [c]; ring
  linear_combination (norm := (field_simp [hc0.ne']; ring_nf; rw [hc', sub_self]))
    (2 / c) * hmass - (2 / c) * hconv

/-- The complementary pole integral is bounded by the difference of the
local density and its two polynomial moments. The omitted exponential
endpoint term is nonnegative even when the inner rate is negative. -/
theorem quarter_gamma_tail_poly_656 {y : ℝ} (hy : 0 ≤ y + 21 / 8) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 21 / 8
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm656 y n t) ≤
      (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z) *
        (2 / c * z ^ 5 - Analysis.logPowerTailPoly (c + 11 / 10) 5 z +
          Analysis.logPowerTailPoly (11 / 10 - c) 5 z) := by
  intro c z
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hne : c ≠ (11 / 10 : ℝ) := by linarith only [hc]
  have hd : (11 / 10 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  have hzero : Analysis.logPowerTailPoly (11 / 10 - c) 5 0 = 120 / ((11 / 10 : ℝ) - c) ^ 6 := by
    norm_num only [Analysis.logPowerTailPoly, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_div, zero_add, Nat.cast_ofNat]
    field_simp [hd]
    norm_num only
  have he := quarter_gamma_tail_conv_656 y n
  change _ = 2 / c * quarterGammaDensity656 z - quarterGammaConvolution656 z c at he
  rw [he, quarter_gamma_conv_expansion_656 hy (by linarith only [hc]) hne, hzero]
  rw [quarterGammaDensity656, ite_eq_left hy]
  have hpos :
    0 ≤ (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-c * z) * (120 / ((11 / 10 : ℝ) - c) ^ 6) := by
    positivity
  nlinarith only [hpos]

/-- Expanding the fifth moment difference separates the baseline, the
three odd-order reciprocal differences, and the two nonpositive even terms. -/
theorem quarter_gamma_poly_terms_656 {c z : ℝ} (hc : 11 / 10 < c) (hz : 0 ≤ z) :
    let a : ℝ := 11 / 10
    let D := fun j : ℕ ↦ 1 / (c - a) ^ j - 1 / (c + a) ^ j
    2 / c * z ^ 5 - Analysis.logPowerTailPoly (c + a) 5 z + Analysis.logPowerTailPoly (a - c) 5 z ≤
      (2 / c - 1 / (c - a) - 1 / (c + a)) * z ^ 5 + 5 * D 2 * z ^ 4 + 60 * D 4 * z ^ 2 +
        120 * D 6 := by
  intro a D
  have hm : 0 < c - a := sub_pos.mpr hc
  have hp : 0 < c + a := by
    dsimp only [a]; linarith only [hc]
  have he (s : ℝ) (hs : s ≠ 0) :
    Analysis.logPowerTailPoly s 5 z =
      z ^ 5 / s + 5 * z ^ 4 / s ^ 2 + 20 * z ^ 3 / s ^ 3 + 60 * z ^ 2 / s ^ 4 + 120 * z / s ^ 5 +
        120 / s ^ 6 := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one]
    field_simp [hs]
    ring
  rw [he _ hp.ne', he _ (sub_ne_zero.mpr (ne_of_lt hc))]
  have h₃ : 0 ≤ 20 * z ^ 3 / (c + a) ^ 3 := by positivity
  have h₅ : 0 ≤ 120 * z / (c + a) ^ 5 := by positivity
  have h₃' : 0 ≤ 20 * z ^ 3 / (c - a) ^ 3 := by positivity
  have h₅' : 0 ≤ 120 * z / (c - a) ^ 5 := by positivity
  rw [show a - c = -(c - a) by ring]
  simp only [Odd.neg_pow (by decide : Odd 3), Odd.neg_pow (by decide : Odd 5),
    Even.neg_pow (by decide : Even 2), Even.neg_pow (by decide : Even 4),
    Even.neg_pow (by decide : Even 6), div_neg, D]
  simp only [div_eq_mul_inv, one_mul] at h₃ h₅ h₃' h₅' ⊢
  nlinarith only [h₃, h₅, h₃', h₅']

/-- Each normalized complementary pole integral is bounded by its
baseline and three odd-order reciprocal differences. -/
theorem quarter_gamma_tail_odd_656 {y : ℝ} (hy : 0 ≤ y + 21 / 8) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 21 / 8
    let a : ℝ := 11 / 10
    let D := fun j : ℕ ↦ 1 / (c - a) ^ j - 1 / (c + a) ^ j
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm656 y n t) ≤
      a ^ 5 / 120 * Real.exp (-a * z) *
        ((2 / c - 1 / (c - a) - 1 / (c + a)) * z ^ 5 + 5 * D 2 * z ^ 4 + 60 * D 4 * z ^ 2 +
          120 * D 6) := by
  intro c z a D
  have hc : (11 / 10 : ℝ) < c := by
    dsimp only [c]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  exact
    (quarter_gamma_tail_poly_656 hy n).trans
      (mul_le_mul_of_nonneg_left (quarter_gamma_poly_terms_656 hc hy) (by positivity))

/-- The later poles yield the certified odd coefficient plus the single
forward term at 4/5, which belongs to the separated first pole. -/
theorem quarter_gamma_odd_hasSum_656 {j : ℕ} (hj : 0 < j) :
    HasSum
      (fun n : ℕ ↦
        (j.factorial : ℝ) *
          (1 / (2 * (n : ℝ) + 5 / 2 - 11 / 10) ^ (j + 1) -
            1 / (2 * (n : ℝ) + 5 / 2 + 11 / 10) ^ (j + 1)))
      (quarterGammaOdd656 j +
        (j.factorial : ℝ) / 2 ^ (j + 1) * (4 / 5 : ℝ) ^ (-((j : ℝ) + 1))) := by
  have hk : 1 < (j : ℝ) + 1 := by linarith only [(show (0 : ℝ) < j from Nat.cast_pos.mpr hj)]
  have ha := (quarter_reciprocal_sum_644 (x := 7 / 10) (by norm_num only) hk).1
  have hb := (quarter_reciprocal_sum_644 (x := 4 / 5) (by norm_num only) hk).1
  have hb' := (summable_nat_add_iff 1).mpr hb
  have hs := (ha.hasSum.sub hb'.hasSum).mul_left ((j.factorial : ℝ) / 2 ^ (j + 1))
  unfold quarterGammaOdd656
  rw [hb.tsum_eq_zero_add, Nat.cast_zero, add_zero]
  rw [show
      (j.factorial : ℝ) / 2 ^ (j + 1) *
            ((∑' n : ℕ, (7 / 10 + n : ℝ) ^ (-((j : ℝ) + 1))) -
              ((4 / 5 : ℝ) ^ (-((j : ℝ) + 1)) +
                ∑' n : ℕ, (4 / 5 + ((n + 1 : ℕ) : ℝ)) ^ (-((j : ℝ) + 1)))) +
          (j.factorial : ℝ) / 2 ^ (j + 1) * (4 / 5 : ℝ) ^ (-((j : ℝ) + 1)) =
        (j.factorial : ℝ) / 2 ^ (j + 1) *
          ((∑' n : ℕ, (7 / 10 + n : ℝ) ^ (-((j : ℝ) + 1))) -
            ∑' n : ℕ, (4 / 5 + ((n + 1 : ℕ) : ℝ)) ^ (-((j : ℝ) + 1)))
      by ring]
  apply hs.congr_fun
  intro n
  have h₁ : 2 * (n : ℝ) + 5 / 2 - 11 / 10 = 2 * (7 / 10 + n) := by ring
  have h₂ : 2 * (n : ℝ) + 5 / 2 + 11 / 10 = 2 * (4 / 5 + ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hkcast : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_one]
  rw [h₁, h₂, mul_pow, mul_pow, hkcast]
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 7 / 10 + n by positivity),
    Real.rpow_neg (show (0 : ℝ) ≤ 4 / 5 + ((n + 1 : ℕ) : ℝ) by positivity), Real.rpow_natCast,
    Real.rpow_natCast]
  simp only [mul_inv_rev, div_eq_mul_inv]
  ring

/-- For two positive real arguments the reciprocal differences sum to
the corresponding real digamma difference. -/
private theorem digamma_diff_hasSum {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    HasSum (fun n : ℕ ↦ 1 / (t + n) - 1 / (s + n)) (digammaReal s - digammaReal t) := by
  have hs' : 0 < (s : ℂ).re := by simpa only [Complex.ofReal_re] using hs
  have ht' : 0 < (t : ℂ).re := by simpa only [Complex.ofReal_re] using ht
  have hsum :=
    (AnalyticNumberTheory.Gamma.summable_digammaResolvent hs'.le).sub
      (AnalyticNumberTheory.Gamma.summable_digammaResolvent ht'.le)
  have h :=
    hsum.hasSum.congr_fun (g := fun n : ℕ ↦ (1 / ((t : ℂ) + n) - 1 / ((s : ℂ) + n)))
      (fun n ↦ by ring)
  rw [h.tsum_eq.symm, ← AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries hs' ht'] at h
  have hr := Complex.reCLM.hasSum h
  simpa only [Complex.reCLM_apply, Complex.sub_re, ← Complex.ofReal_natCast, ← Complex.ofReal_add,
    ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re, digammaReal] using hr

/-- The constant terms from the later poles sum to the average of the
shifted digamma values minus the digamma value at the first tail index. -/
theorem quarter_gamma_baseline_sum_656 :
    HasSum
      (fun n : ℕ ↦
        let c : ℝ := 2 * (n : ℝ) + 5 / 2
        2 / c - 1 / (c - 11 / 10) - 1 / (c + 11 / 10))
      ((digammaReal (7 / 10) + digammaReal (9 / 5)) / 2 - digammaReal (5 / 4)) := by
  have ha := digamma_diff_hasSum (s := 7 / 10) (t := 5 / 4) (by norm_num only) (by norm_num only)
  have hb := digamma_diff_hasSum (s := 9 / 5) (t := 5 / 4) (by norm_num only) (by norm_num only)
  have h := (ha.add hb).mul_left (1 / 2)
  have he :
    (1 / 2 : ℝ) *
        (digammaReal (7 / 10) - digammaReal (5 / 4) + (digammaReal (9 / 5) - digammaReal (5 / 4))) =
      (digammaReal (7 / 10) + digammaReal (9 / 5)) / 2 - digammaReal (5 / 4) := by
    ring
  rw [← he]
  apply h.congr_fun
  intro n
  dsimp only
  have h₀ : 2 * (n : ℝ) + 5 / 2 = 2 * (5 / 4 + n) := by ring
  have h₁ : 2 * (n : ℝ) + 5 / 2 - 11 / 10 = 2 * (7 / 10 + n) := by ring
  have h₂ : 2 * (n : ℝ) + 5 / 2 + 11 / 10 = 2 * (9 / 5 + n) := by ring
  rw [h₁, h₂, h₀]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The gamma baseline and the summed pole constants reduce to the two
certified digamma arguments after the forward first-pole term is removed. -/
theorem quarter_gamma_baseline_cancel_656 :
    (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4 +
          ((digammaReal (7 / 10) + digammaReal (9 / 5)) / 2 - digammaReal (5 / 4)) -
        1 / (8 / 5) =
      (digammaReal (7 / 10) + digammaReal (4 / 5)) / 2 - Real.log Real.pi := by
  have h₁ := LLS.PaperStatements.re_digamma_real_add_one (b := 1 / 4) (by norm_num only)
  have h₂ := LLS.PaperStatements.re_digamma_real_add_one (b := 4 / 5) (by norm_num only)
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num only] at h₁
  rw [show (4 / 5 : ℝ) + 1 = 9 / 5 by norm_num only] at h₂
  have hc : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hc] at h₁
  unfold digammaReal
  linarith only [h₁, h₂]

/-- The normalized sum of all later pole integrals is bounded by the
summed baseline and odd coefficients, including the forward corrections. -/
theorem quarter_gamma_tail_sum_656 {y : ℝ} (hy : 0 ≤ y + 21 / 8) :
    let z := y + 21 / 8
    let A := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z)
    let B := (digammaReal (7 / 10) + digammaReal (9 / 5)) / 2 - digammaReal (5 / 4)
    (1 / (2 * Real.pi)) * (∑' n : ℕ, ∫ t : ℝ, gammaTailTerm656 y n t) ≤
      A *
        (B * z ^ 5 + 5 * quarterGammaOdd656 1 * z ^ 4 + 10 * quarterGammaOdd656 3 * z ^ 2 +
          quarterGammaOdd656 5 +
          5 * z ^ 4 / (8 / 5) ^ 2 +
          60 * z ^ 2 / (8 / 5) ^ 4 +
          120 / (8 / 5) ^ 6) := by
  intro z A B
  have h₁ := quarter_gamma_odd_hasSum_656 (j := 1) (by decide)
  have h₃ := quarter_gamma_odd_hasSum_656 (j := 3) (by decide)
  have h₅ := quarter_gamma_odd_hasSum_656 (j := 5) (by decide)
  let p := fun n : ℕ ↦
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let a : ℝ := 11 / 10
    let D := fun j : ℕ ↦ 1 / (c - a) ^ j - 1 / (c + a) ^ j
    A *
      ((2 / c - 1 / (c - a) - 1 / (c + a)) * z ^ 5 + 5 * D 2 * z ^ 4 + 60 * D 4 * z ^ 2 + 120 * D 6)
  have hp :=
    ((((quarter_gamma_baseline_sum_656.mul_right (z ^ 5)).add (h₁.mul_left (5 * z ^ 4))).add
              (h₃.mul_left (10 * z ^ 2))).add
          h₅).mul_left
      A
  have hps :=
    hp.congr_fun (g := p) fun n ↦ by
      dsimp only [p]
      norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd]
      ring
  have hi : Summable (fun n : ℕ ↦ ∫ t : ℝ, gammaTailTerm656 y n t) :=
    (gamma_tail_norm_summable_656 y).of_norm_bounded fun n ↦
      MeasureTheory.norm_integral_le_integral_norm _
  have hsum :=
    (hi.mul_left (1 / (2 * Real.pi))).tsum_le_tsum (fun n ↦ quarter_gamma_tail_odd_656 hy n)
      hps.summable
  rw [tsum_mul_left, hps.tsum_eq] at hsum
  convert hsum using 1
  push_cast
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd,
    Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 4 / 5), Real.rpow_ofNat]
  ring

/-- For an even character at a nonnegative shifted logarithmic scale, the
central Gamma pair is bounded by the endpoint-weight polynomial minus the
truncated first-pole moment. The forward terms cancel in the pole expansion. -/
theorem quarter_gamma_pair_upper_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hz : 0 ≤ Real.log x + 21 / 8) :
    let z := Real.log x + 21 / 8
    let A := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z)
    (centralGammaPair656 χ x).re ≤
      A *
          (((digammaReal (7 / 10) + digammaReal (4 / 5)) / 2 - Real.log Real.pi) * z ^ 5 +
            5 * quarterGammaOdd656 1 * z ^ 4 +
            10 * quarterGammaOdd656 3 * z ^ 2 +
            quarterGammaOdd656 5) -
        quarterGammaFirst656 z := by
  intro z A
  let y := Real.log x
  have hz₀ : 0 ≤ z := hz
  have hf := congrArg Complex.re (quarter_main_fourier_656 y)
  have hre := Complex.reCLM.integral_comp_comm (quarter_main_phase_regular_656 y).2
  change
    (∫ t : ℝ, gammaPhase656 y t) =
      (∫ t : ℝ,
          quarterKernel656.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hf
  rw [← hre,
    show -y = (21 / 8 : ℝ) - z by
      dsimp only [y, z]; ring,
    quarter_profile_shift_656, quarterGammaDensity656, ite_eq_left hz₀] at hf
  have hm : (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaPhase656 y t) = A * z ^ 5 := by
    dsimp only [A]
    linarith only [hf]
  have hp :
    z ^ 5 / (8 / 5) + 5 * z ^ 4 / (8 / 5) ^ 2 + 60 * z ^ 2 / (8 / 5) ^ 4 + 120 / (8 / 5) ^ 6 ≤
      Analysis.logPowerTailPoly (8 / 5) 5 z := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one]
    nlinarith only [pow_nonneg hz₀ 3, hz₀]
  have hmul :=
    mul_le_mul_of_nonneg_left hp
      (show 0 ≤ A by
        dsimp only [A]; positivity)
  have hr := quarter_first_resolvent_eq_656 (y := y) hz₀
  have ht := quarter_gamma_tail_sum_656 (y := y) hz₀
  have hb := congrArg (fun v : ℝ ↦ A * z ^ 5 * v) quarter_gamma_baseline_cancel_656
  have hs := quarter_gamma_first_split_656 χ he hx
  dsimp only at hs ht
  rw [hs]
  dsimp only [A, z, y] at *
  nlinarith only [congrArg
      (fun v : ℝ ↦ ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4) * v) hm,
    hmul, hr, ht, hb]

/-- Over a nonnegative scale interval, the first-pole term is bounded below
by the fifth moment at the left endpoint and the exponential at the right. -/
theorem quarter_first_interval_lower_656 {l z u : ℝ} (hl : 0 ≤ l) (hlz : l ≤ z) (hzu : z ≤ u) :
    ((11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(1 / 2) * u)) *
        (Analysis.logPowerTailPoly (3 / 5) 5 0 -
          Real.exp (-(3 / 5) * l) * Analysis.logPowerTailPoly (3 / 5) 5 l) ≤
      quarterGammaFirst656 z := by
  let f := fun v : ℝ ↦ v ^ 5 * Real.exp (-(3 / 5) * v)
  have hf := Analysis.exponential_moment_integrable (r := (3 / 5 : ℝ)) (by norm_num only) 5
  have hi : MeasureTheory.IntegrableOn f (Set.Ioc 0 z) := hf.mono_set Set.Ioc_subset_Ioi_self
  have hn v (hv : v ∈ Set.Ioc (0 : ℝ) z) : 0 ≤ f v :=
    mul_nonneg (pow_nonneg hv.1.le _) (Real.exp_pos _).le
  have hm :=
    MeasureTheory.setIntegral_mono_set hi
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hn)
      (Filter.Eventually.of_forall fun v (hv : v ∈ Set.Ioc (0 : ℝ) l) ↦ ⟨hv.1, hv.2.trans hlz⟩)
  have hnon : 0 ≤ ∫ v in Set.Ioc (0 : ℝ) l, f v :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioc fun v hv ↦ hn v ⟨hv.1, hv.2.trans hlz⟩
  have he : Real.exp (-(1 / 2 : ℝ) * u) ≤ Real.exp (-(1 / 2) * z) :=
    Real.exp_le_exp.mpr (by linarith only [hzu])
  rw [quarterGammaFirst656, ← Analysis.exponential_moment_interval (by norm_num only) hl 5]
  exact
    mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num only)) hm hnon
      (mul_nonneg (by norm_num only) (Real.exp_pos _).le)

/-- The upper bound for the central Gamma pair also bounds the sum of the
two contour contributions for an even self-inverse nonprincipal character. -/
theorem quarter_gamma_contours_upper_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {x : ℝ} (hx : 1 ≤ x) :
    let z := Real.log x + 21 / 8
    let A := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z)
    (quarterMainArch656 χ x + quarterRightGamma656 χ x).re ≤
      A *
          (((digammaReal (7 / 10) + digammaReal (4 / 5)) / 2 - Real.log Real.pi) * z ^ 5 +
            5 * quarterGammaOdd656 1 * z ^ 4 +
            10 * quarterGammaOdd656 3 * z ^ 2 +
            quarterGammaOdd656 5) -
        quarterGammaFirst656 z := by
  dsimp only
  rw [quarter_gamma_contours_central_656 χ hn hi he hx]
  exact
    quarter_gamma_pair_upper_656 χ he (zero_lt_one.trans_le hx)
      (add_nonneg (Real.log_nonneg hx) (by norm_num only))

/-- The baseline coefficient of the section 132 central Gamma bound is at
most -2.237. The two digamma enclosures use 48 reciprocal terms each. -/
theorem quarter_gamma_baseline_upper_656 :
    (digammaReal (7 / 10) + digammaReal (4 / 5)) / 2 - Real.log Real.pi ≤ -2.237 := by
  have hl :=
    (AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
        (show
          AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (7 / 10) 48 5 32 (-2) (-1.21998) =
            true
          from by decide +kernel)).2
  have hr :=
    (AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck_sound
        (show
          AnalyticNumberTheory.Gamma.rationalDigammaIntervalCheck (4 / 5) 48 5 32 (-2) (-0.96496) =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg, Rat.cast_ofScientific,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hl hr
  unfold digammaReal
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [hl, hr, Analysis.log_pi_ge_2096_div_1831]

/-- The rational majorants for the odd derivatives imply
the three constants used in the normalized gamma polynomial. -/
theorem quarter_gamma_odd_caps_656 {g : ℕ → ℝ}
    (hg :
      ∀ j ∈ ({1, 3, 5} : Finset ℕ),
        |g j| ≤
          (1 / 10 : ℝ) / 2 ^ (j + 1) *
            (((j + 1).factorial : ℝ) / (7 / 10) ^ (j + 2) +
              (j.factorial : ℝ) / (7 / 10) ^ (j + 1))) :
    |g 1| ≤ 0.197 ∧ |g 3| ≤ 1.049 ∧ |g 5| ≤ 16 := by
  refine ⟨(hg 1 (by decide)).trans ?_, (hg 3 (by decide)).trans ?_, (hg 5 (by decide)).trans ?_⟩
  all_goals norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.mul_one]

/-- The reciprocal-series coefficients of orders one, three and five
obey the rational caps in the section 132 gamma polynomial. -/
theorem quarter_gamma_odd_series_656 :
    |quarterGammaOdd656 1| ≤ 0.197 ∧
      |quarterGammaOdd656 3| ≤ 1.049 ∧ |quarterGammaOdd656 5| ≤ 16 := by
  apply quarter_gamma_odd_caps_656
  intro j hj
  have hj₀ : 0 < j := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl | rfl <;> decide
  have hj₁ : 1 < (j : ℝ) + 1 := by linarith only [(show (0 : ℝ) < j from Nat.cast_pos.mpr hj₀)]
  have h :=
    quarter_reciprocal_diff_644 (x := 7 / 10) (y := 4 / 5) (by norm_num only) (by norm_num only) hj₁
  dsimp only at h
  unfold quarterGammaOdd656
  rw [abs_of_nonneg (mul_nonneg (by positivity) h.1)]
  refine (mul_le_mul_of_nonneg_left h.2 (by positivity)).trans (le_of_eq ?_)
  rw [show (4 / 5 : ℝ) - 7 / 10 = 1 / 10 by norm_num only, ← Nat.cast_succ, ← Nat.cast_succ,
    Real.rpow_neg (by norm_num only), Real.rpow_neg (by norm_num only), Real.rpow_natCast,
    Real.rpow_natCast, Nat.factorial_succ, Nat.cast_mul]
  field_simp [show ((j + 1 : ℕ) : ℝ) ≠ 0 by positivity]

/-- For logarithmic argument at least 14, the three prescribed odd-order
coefficient bounds raise the zero-order gamma bound by less than 0.077. -/
theorem quarter_gamma_poly_upper_656 {z g₁ g₃ g₅ : ℝ} (hz : 14 ≤ z) (h₁ : |g₁| ≤ 0.197)
    (h₃ : |g₃| ≤ 1.049) (h₅ : |g₅| ≤ 16) :
    (digammaReal (7 / 10) + digammaReal (4 / 5)) / 2 - Real.log Real.pi + 5 * g₁ / z +
        10 * g₃ / z ^ 3 +
        g₅ / z ^ 5 ≤
      -2.16 := by
  have hb (k : ℕ) {a b : ℝ} (hab : a ≤ b) (h₀ : 0 ≤ b) : a / z ^ k ≤ b / 14 ^ k := by
    have hp := pow_pos (by linarith only [hz] : 0 < z) k
    exact
      (div_le_div_of_nonneg_right hab hp.le).trans
        (div_le_div_of_nonneg_left h₀ (pow_pos (by norm_num only) k)
          (pow_le_pow_left₀ (by norm_num only) hz k))
  have ha :=
    hb 1 (mul_le_mul_of_nonneg_left ((le_abs_self g₁).trans h₁) (by norm_num only : (0 : ℝ) ≤ 5))
      (by norm_num only)
  have hc :=
    hb 3 (mul_le_mul_of_nonneg_left ((le_abs_self g₃).trans h₃) (by norm_num only : (0 : ℝ) ≤ 10))
      (by norm_num only)
  have hd := hb 5 ((le_abs_self g₅).trans h₅) (by norm_num only)
  norm_num only [pow_one] at ha
  linarith only [quarter_gamma_baseline_upper_656, ha, hc, hd]

/-- At shifted logarithm at least 14, the even Gamma pair is at most
minus 2.16 times the endpoint density minus the first-pole moment. -/
theorem quarter_gamma_density_upper_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) (hz : 14 ≤ Real.log x + 21 / 8) :
    let z := Real.log x + 21 / 8
    let A := (11 / 10 : ℝ) ^ 5 / 120 * Real.exp (-(11 / 10) * z)
    (centralGammaPair656 χ x).re ≤ -2.16 * (A * z ^ 5) - quarterGammaFirst656 z := by
  intro z A
  have hz₁ : 14 ≤ z := hz
  have hz₀ : 0 < z := by linarith only [hz₁]
  obtain ⟨h₁, h₃, h₅⟩ := quarter_gamma_odd_series_656
  have h := quarter_gamma_poly_upper_656 hz₁ h₁ h₃ h₅
  have hpoly := mul_le_mul_of_nonneg_right h (pow_nonneg hz₀.le 5)
  have hclear (B g₁ g₃ g₅ : ℝ) :
    (B + 5 * g₁ / z + 10 * g₃ / z ^ 3 + g₅ / z ^ 5) * z ^ 5 =
      B * z ^ 5 + 5 * g₁ * z ^ 4 + 10 * g₃ * z ^ 2 + g₅ := by
    field_simp [hz₀.ne']
  rw [hclear] at hpoly
  have hA : 0 ≤ A := by
    dsimp only [A]; positivity
  have hscaled := sub_le_sub_right (mul_le_mul_of_nonneg_left hpoly hA) (quarterGammaFirst656 z)
  exact (quarter_gamma_pair_upper_656 χ he hx hz₀.le).trans (hscaled.trans_eq (by ring))

/-- On the section 132 radius range, the principal Gamma pair is bounded
in terms of the physical weight at one and the first-pole correction.
These are the quantities in the broad comparison. -/
theorem quarter_principal_gamma_upper_656 {r : ℝ} (hr : 322 ≤ r) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
  have hpos : 0 < r := (by norm_num only : (0 : ℝ) < 322).trans_le hr
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  simp only [Rat.cast_div, Rat.cast_ofNat] at hL
  have hz : 14 ≤ Real.log (r ^ 2) + 21 / 8 := by
    rw [Real.log_pow]
    linarith only [hL, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr]
  have he : (1 : DirichletCharacter ℂ 1).Even := DirichletCharacter.even_one
  have h := quarter_gamma_density_upper_656 (1 : DirichletCharacter ℂ 1) he (sq_pos_of_pos hpos) hz
  dsimp only at h
  unfold quarterWeight656
  simp only [Real.sqrt_one, div_one, one_mul, one_div, Real.log_inv, sub_neg_eq_add]
  convert h using 1
  ring_nf

end PseudoPrime.PrimeTestBounds.MillerRabin
