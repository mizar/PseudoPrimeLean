/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.LLS.PaperStatements.GammaScalarArchimedeanBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaCentral644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPole644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainGamma644
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaBaseline

/-! # Pole series for the section 122 central Gamma integral -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Real oscillatory factor of the section 31 kernel at logarithmic scale y. -/
noncomputable def gammaPhase644 (y t : ℝ) : ℝ :=
  (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)).re

/-- For an even character, the sum of the reflected and right central
Gamma integrands equals the real digamma factor times the complex kernel phase. -/
theorem even_gamma_integrand_eq_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (x t : ℝ) :
    reflectedGammaIntegrand644 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
        gammaIntegrand644 χ x ((0 : ℂ) + t * Complex.I) =
      (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi : ℝ) :
          ℂ) *
        (quarterKernel644.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
  have hs : star (Complex.I * (t : ℂ) + 1 / 2) = 1 / 2 - Complex.I * t := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
      map_one, map_ofNat]
    ring
  have hd := refined_even_gamma_real_digamma χ he t
  unfold reflectedGammaIntegrand644 gammaIntegrand644
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
normalized integral of the real digamma weight against the section 122 phase.
Absolute integrability permits commuting the real part with the integral. -/
theorem central_real_phase_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even) {x : ℝ}
    (hx : 0 < x) :
    let f := fun t : ℝ ↦
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
        gammaPhase644 (Real.log x) t
    MeasureTheory.Integrable f ∧ (centralGammaPair644 χ x).re = (∫ t : ℝ, f t) / (2 * Real.pi) := by
  let P := gammaPhase644 (Real.log x)
  let F : ℝ → ℂ := fun t ↦
    reflectedGammaIntegrand644 χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
      gammaIntegrand644 χ x ((0 : ℂ) + t * Complex.I)
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand644 χ⁻¹ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand644, mul_comm Complex.I, Complex.ofReal_zero] using
      (reflected_gamma_line_integrable_644 χ⁻¹ (c := 0) hx (by norm_num only) (by norm_num only)
        (by norm_num only))
  have hi2 :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaIntegrand644 χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [gammaIntegrand644, mul_comm Complex.I, Complex.ofReal_zero] using
      (gamma_line_integrable_644 χ (c := 0) hx (by norm_num only) (by norm_num only))
  have hFi : MeasureTheory.Integrable F := hi1.add hi2
  have hp (t : ℝ) : (x : ℂ) ^ (Complex.I * t) = Complex.exp (Complex.I * (t : ℂ) * Real.log x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le]
    congr 1
    ring
  have hpoint (t : ℝ) :
    (F t).re =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t := by
    dsimp only [F, P, gammaPhase644]
    rw [even_gamma_integrand_eq_644 χ he x t, hp]
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
    (centralGammaPair644 χ x).re =
      (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) /
        (2 * Real.pi) := by
    rw [← central_gamma_pair_eq_644 χ he hx, ← mul_add, ← MeasureTheory.integral_add hi1 hi2]
    change ((((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← hr, hint]
    ring
  exact ⟨hG, hpair⟩

/-- The real phase associated with the main kernel is continuous and integrable. -/
theorem gamma_phase_integrable_644 (y : ℝ) :
    Continuous (gammaPhase644 y) ∧ MeasureTheory.Integrable (gammaPhase644 y) := by
  exact
    ⟨Complex.continuous_re.comp (quarter_main_phase_regular_644 y).1,
      (quarter_main_phase_regular_644 y).2.re⟩

/-- The second height moment of the sixth-pole kernel is integrable. Scale
the difference of the integrable second and third Cauchy powers. -/
theorem second_integrable_644 :
    MeasureTheory.Integrable (fun t : ℝ ↦ t ^ 2 * ‖quarterKernel644.function (Complex.I * t)‖) := by
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
              (by norm_num only : (100 / 107 : ℝ) ≠ 0)).mpr
          hn).const_mul
      (107 / 100 : ℝ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [quarter_zero_norm_644]
  have h1 : (107 / 100 : ℝ) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h2 : 1 + ((100 / 107 : ℝ) * t) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The term after the first pole in the even digamma correction, multiplied by the
real oscillatory phase. Its index starts at the pole with rate `5/2`. -/
noncomputable def gammaTailTerm644 (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((t / 2) ^ 2 / ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2))) *
    gammaPhase644 y t

/-- Each signed tail term is absolutely bounded by the second kernel moment times
the corresponding inverse cube. This is the majorant for termwise integration. -/
theorem gamma_tail_term_bound_644 (y : ℝ) (n : ℕ) (t : ℝ) :
    ‖gammaTailTerm644 y n t‖ ≤
      (2 / (2 * (n : ℝ) + 5 / 2) ^ 3) * (t ^ 2 * ‖quarterKernel644.function (Complex.I * t)‖) := by
  have ha : 0 < (1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ) := by positivity
  have hd :
    0 ≤
      (t / 2) ^ 2 /
        ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg ha.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hp : |gammaPhase644 y t| ≤ ‖quarterKernel644.function (Complex.I * t)‖ := by
    have h :=
      Complex.abs_re_le_norm
        (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y))
    rw [norm_mul, Complex.norm_exp] at h
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero, mul_one] at h
    exact h
  rw [gammaTailTerm644, norm_mul, Real.norm_eq_abs, abs_of_nonneg hd, Real.norm_eq_abs]
  have h :=
    mul_le_mul (target028_gamma_correction_term t n) hp (abs_nonneg _)
      (le_trans hd (target028_gamma_correction_term t n))
  convert h using 1
  ring

/-- Each tail term is integrable: its continuous integrand is dominated by the
integrable second moment of the sixth-pole kernel. -/
theorem gamma_tail_term_integrable_644 (y : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (gammaTailTerm644 y n) := by
  have hd (t : ℝ) :
    (1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2) ≠ 0 := by
    positivity
  have hc : Continuous (gammaTailTerm644 y n) := by
    unfold gammaTailTerm644
    apply Continuous.mul
    · exact
        ((continuous_id.div_const 2).pow 2).div
          (continuous_const.mul (continuous_const.add ((continuous_id.div_const 2).pow 2))) hd
    · exact (gamma_phase_integrable_644 y).1
  apply
    (second_integrable_644.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (gamma_tail_term_bound_644 y n)

/-- The integrals of the absolute tail terms form a convergent series, using the
summable inverse-cube bound for the pole rates. -/
theorem gamma_tail_norm_summable_644 (y : ℝ) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖gammaTailTerm644 y n t‖) := by
  let C : ℝ := ∫ t : ℝ, t ^ 2 * ‖quarterKernel644.function (Complex.I * t)‖
  have hs : Summable (fun n : ℕ ↦ (2 * C) * (1 / (2 * (n : ℝ) + 5 / 2) ^ 3)) :=
    target028_gamma_pole_tail_summable.mul_left (2 * C)
  apply hs.of_nonneg_of_le
  · intro n
    exact MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _)
  · intro n
    have hi := gamma_tail_term_integrable_644 y n
    have hmajor := second_integrable_644.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)
    have h := MeasureTheory.integral_mono hi.norm hmajor (gamma_tail_term_bound_644 y n)
    rw [MeasureTheory.integral_const_mul] at h
    dsimp only [C]
    convert h using 1
    ring

/-- The oscillatory even-Gamma tail can be integrated term by term: the individual
terms are integrable and their integral norms form a summable series. -/
theorem gamma_tail_integral_tsum_644 (y : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, gammaTailTerm644 y n t) = ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm644 y n t := by
  exact
    (MeasureTheory.integral_tsum_of_summable_integral_norm (gamma_tail_term_integrable_644 y)
        (gamma_tail_norm_summable_644 y)).symm

/-- The oscillatory digamma increment after removing its first pole equals the
convergent series of signed tail terms. The identity separates the first term of
the vertical digamma expansion and distributes the phase over the remaining sum. -/
theorem gamma_tail_eq_series_644 (y t : ℝ) :
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        gammaPhase644 y t =
      ∑' n : ℕ, gammaTailTerm644 y n t := by
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
  simp only [gammaTailTerm644, tsum_mul_right]
  have he := congrArg (fun x : ℝ ↦ (x - (4 - 1 / (1 / 4 + t ^ 2))) * gammaPhase644 y t) h
  simpa only [add_sub_cancel_left, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using he

/-- The actual phase divided by the first-pole denominator is integrable.
The reciprocal denominator is continuous and bounded by four. -/
theorem resolvent_integrable_644 (y : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase644 y t / (1 / 4 + t ^ 2)) := by
  have hden (t : ℝ) : 1 / 4 + t ^ 2 ≠ (0 : ℝ) := by nlinarith only [sq_nonneg t]
  have hc : Continuous (fun t : ℝ ↦ (1 / 4 + t ^ 2)⁻¹) := by
    exact (continuous_const.add (continuous_id.pow 2)).inv₀ hden
  have hi := (gamma_phase_integrable_644 y).2
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
theorem quarter_gamma_first_split_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    let y := Real.log x
    let P := gammaPhase644 y
    let B := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4
    (centralGammaPair644 χ x).re =
      (1 / (2 * Real.pi)) *
        (B * (∫ t : ℝ, P t) - (∫ t : ℝ, P t / (1 / 4 + t ^ 2)) +
          ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm644 y n t) := by
  intro y P B
  obtain ⟨hG, hcentral⟩ := central_real_phase_644 χ he hx
  let G := fun t : ℝ ↦
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t
  let R := fun t : ℝ ↦ P t / (1 / 4 + t ^ 2)
  have hP := (gamma_phase_integrable_644 y).2
  have hR := resolvent_integrable_644 y
  have hsum : (∫ t : ℝ, G t - B * P t + R t) = ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm644 y n t := by
    rw [← gamma_tail_integral_tsum_644 y]
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    dsimp only
    rw [← gamma_tail_eq_series_644 y t]
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
  have h₁ : (centralGammaPair644 χ x).re = (∫ t : ℝ, G t) / (2 * Real.pi) := hcentral
  rw [h₁, ← hsum]
  ring

/-- For a positive pole rate, the real phase resolvent is the real part of the
complex resolvent integral. The reciprocal denominator is bounded by `1 / c²`. -/
theorem phase_resolvent_644 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, gammaPhase644 y t / (c ^ 2 + t ^ 2)) =
      (∫ t : ℝ,
          (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hcont : Continuous (fun t : ℝ ↦ (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t ↦ (hden t).ne'))
  have hi := (quarter_main_phase_regular_644 y).2
  have hm := hi.mul_bdd (c := (c ^ 2)⁻¹) hcont.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (c ^ 2)⁻¹ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hden t).le)]
    exact inv_anti₀ (sq_pos_of_pos hc) (le_add_of_nonneg_right (sq_nonneg t))
  have hr := Complex.reCLM.integral_comp_comm (hm hb)
  change
    (∫ t : ℝ,
        (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) =
      _ at hr
  have he :
    (∫ t : ℝ, gammaPhase644 y t / (c ^ 2 + t ^ 2)) =
      ∫ t : ℝ,
        (quarterKernel644.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [gammaPhase644, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  rw [he, hr]
  simp only [one_div]
  rfl

/-- On the section 122 radius interval, the actual gamma contour pair
is bounded above by its baseline and complementary pole series minus the
certified first-pole contribution. -/
theorem quarter_gamma_tail_reduce_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    let y := 2 * Real.log r
    let B := (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4
    (quarterMainArch644 χ (r ^ 2) + quarterRightGamma644 χ (r ^ 2)).re ≤
      (1 / (2 * Real.pi)) *
          (B * (∫ t : ℝ, gammaPhase644 y t) + ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm644 y n t) -
        0.02712 := by
  intro y B
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hx : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr₁
  have hp := quarter_first_resolvent_rows_644 hr
  have hphase := phase_resolvent_644 y (c := (1 / 2 : ℝ)) (by norm_num only)
  norm_num only at hphase
  have hs := quarter_gamma_first_split_644 χ he (zero_lt_one.trans_le hx)
  dsimp only at hs
  rw [Real.log_pow, Nat.cast_ofNat] at hs
  rw [quarter_gamma_contours_central_644 χ hn hi he hx, hs]
  dsimp only [y, B] at hphase ⊢
  rw [hphase]
  linarith only [hp]

/-- Each complementary pole integral is the normalized density contribution
minus the corresponding positive-support convolution. -/
theorem quarter_gamma_tail_conv_644 (y : ℝ) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 2687 / 1000
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm644 y n t) =
      (2 / c) * quarterGammaDensity644 z - quarterGammaConvolution644 z c := by
  let c : ℝ := 2 * (n : ℝ) + 5 / 2
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hc0 : 0 < c := by linarith only [hc]
  have hden (t : ℝ) : c ^ 2 + t ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (sq_nonneg t)).ne'
  have he (t : ℝ) :
    gammaTailTerm644 y n t =
      (2 / c) * (gammaPhase644 y t - c ^ 2 * (gammaPhase644 y t / (c ^ 2 + t ^ 2))) := by
    dsimp only [gammaTailTerm644, c]
    push_cast
    field_simp
    ring
  have hr (t : ℝ) :
    gammaPhase644 y t / (c ^ 2 + t ^ 2) =
      (c ^ 2)⁻¹ * (gammaPhase644 y t - (c / 2) * gammaTailTerm644 y n t) := by
    rw [he]
    field_simp
    ring
  have hiP := (gamma_phase_integrable_644 y).2
  have hiF := gamma_tail_term_integrable_644 y n
  have hiR : MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase644 y t / (c ^ 2 + t ^ 2)) := by
    apply ((hiP.sub (hiF.const_mul (c / 2))).const_mul (c ^ 2)⁻¹).congr
    exact Filter.Eventually.of_forall (fun t ↦ (hr t).symm)
  have hint :
    (∫ t : ℝ, gammaTailTerm644 y n t) =
      (2 / c) *
        ((∫ t : ℝ, gammaPhase644 y t) - c ^ 2 * ∫ t : ℝ, gammaPhase644 y t / (c ^ 2 + t ^ 2)) := by
    have hfun :
      gammaTailTerm644 y n = fun t ↦
        (2 / c) * (gammaPhase644 y t - c ^ 2 * (gammaPhase644 y t / (c ^ 2 + t ^ 2))) :=
      funext he
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hiP (hiR.const_mul _),
      MeasureTheory.integral_const_mul]
  have hmass := congrArg Complex.re (quarter_main_fourier_644 y)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hmass
  have hre := Complex.reCLM.integral_comp_comm (quarter_main_phase_regular_644 y).2
  change
    (∫ t : ℝ, gammaPhase644 y t) =
      (∫ t : ℝ,
          quarterKernel644.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hre
  rw [← hre] at hmass
  change
    1 / (2 * Real.pi) * (∫ t : ℝ, gammaPhase644 y t) =
      Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (Real.exp (-y)) at hmass
  have harg : (2687 / 1000 : ℝ) - (y + 2687 / 1000) = -y := by ring
  rw [← harg, quarter_profile_shift_644] at hmass
  have hconv := quarter_gamma_pole_real_644 y hc0
  rw [← phase_resolvent_644 y hc0] at hconv
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
theorem quarter_gamma_tail_poly_644 {y : ℝ} (hy : 0 ≤ y + 2687 / 1000) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 2687 / 1000
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm644 y n t) ≤
      (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) *
        (2 / c * z ^ 5 - Analysis.logPowerTailPoly (c + 107 / 100) 5 z +
          Analysis.logPowerTailPoly (107 / 100 - c) 5 z) := by
  intro c z
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hne : c ≠ (107 / 100 : ℝ) := by linarith only [hc]
  have hd : (107 / 100 : ℝ) - c ≠ 0 := sub_ne_zero.mpr hne.symm
  have hzero : Analysis.logPowerTailPoly (107 / 100 - c) 5 0 = 120 / ((107 / 100 : ℝ) - c) ^ 6 := by
    norm_num only [Analysis.logPowerTailPoly, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_div, zero_add, Nat.cast_ofNat]
    field_simp [hd]
    norm_num only
  have he := quarter_gamma_tail_conv_644 y n
  change _ = 2 / c * quarterGammaDensity644 z - quarterGammaConvolution644 z c at he
  rw [he, quarter_gamma_conv_expansion_644 hy (by linarith only [hc]) hne, hzero]
  rw [quarterGammaDensity644, ite_eq_left hy]
  have hpos :
    0 ≤ (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-c * z) * (120 / ((107 / 100 : ℝ) - c) ^ 6) := by
    positivity
  nlinarith only [hpos]

/-- Expanding the fifth moment difference separates the baseline, the
three odd-order reciprocal differences, and the two nonpositive even terms. -/
theorem quarter_gamma_poly_terms_644 {c z : ℝ} (hc : 107 / 100 < c) (hz : 0 ≤ z) :
    let a : ℝ := 107 / 100
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
theorem quarter_gamma_tail_odd_644 {y : ℝ} (hy : 0 ≤ y + 2687 / 1000) (n : ℕ) :
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let z := y + 2687 / 1000
    let a : ℝ := 107 / 100
    let D := fun j : ℕ ↦ 1 / (c - a) ^ j - 1 / (c + a) ^ j
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaTailTerm644 y n t) ≤
      a ^ 5 / 120 * Real.exp (-a * z) *
        ((2 / c - 1 / (c - a) - 1 / (c + a)) * z ^ 5 + 5 * D 2 * z ^ 4 + 60 * D 4 * z ^ 2 +
          120 * D 6) := by
  intro c z a D
  have hc : (107 / 100 : ℝ) < c := by
    dsimp only [c]
    linarith only [Nat.cast_nonneg (α := ℝ) n]
  exact
    (quarter_gamma_tail_poly_644 hy n).trans
      (mul_le_mul_of_nonneg_left (quarter_gamma_poly_terms_644 hc hy) (by positivity))

/-- The later poles yield the certified odd coefficient plus the single
forward term at 157/200, which belongs to the separated first pole. -/
theorem quarter_gamma_odd_hasSum_644 {j : ℕ} (hj : 0 < j) :
    HasSum
      (fun n : ℕ ↦
        (j.factorial : ℝ) *
          (1 / (2 * (n : ℝ) + 5 / 2 - 107 / 100) ^ (j + 1) -
            1 / (2 * (n : ℝ) + 5 / 2 + 107 / 100) ^ (j + 1)))
      (quarterGammaOdd644 j +
        (j.factorial : ℝ) / 2 ^ (j + 1) * (157 / 200 : ℝ) ^ (-((j : ℝ) + 1))) := by
  have hk : 1 < (j : ℝ) + 1 := by linarith only [(show (0 : ℝ) < j from Nat.cast_pos.mpr hj)]
  have ha := (quarter_reciprocal_sum_644 (x := 143 / 200) (by norm_num only) hk).1
  have hb := (quarter_reciprocal_sum_644 (x := 157 / 200) (by norm_num only) hk).1
  have hb' := (summable_nat_add_iff 1).mpr hb
  have hs := (ha.hasSum.sub hb'.hasSum).mul_left ((j.factorial : ℝ) / 2 ^ (j + 1))
  unfold quarterGammaOdd644
  rw [hb.tsum_eq_zero_add, Nat.cast_zero, add_zero]
  rw [show
      (j.factorial : ℝ) / 2 ^ (j + 1) *
            ((∑' n : ℕ, (143 / 200 + n : ℝ) ^ (-((j : ℝ) + 1))) -
              ((157 / 200 : ℝ) ^ (-((j : ℝ) + 1)) +
                ∑' n : ℕ, (157 / 200 + ((n + 1 : ℕ) : ℝ)) ^ (-((j : ℝ) + 1)))) +
          (j.factorial : ℝ) / 2 ^ (j + 1) * (157 / 200 : ℝ) ^ (-((j : ℝ) + 1)) =
        (j.factorial : ℝ) / 2 ^ (j + 1) *
          ((∑' n : ℕ, (143 / 200 + n : ℝ) ^ (-((j : ℝ) + 1))) -
            ∑' n : ℕ, (157 / 200 + ((n + 1 : ℕ) : ℝ)) ^ (-((j : ℝ) + 1)))
      by ring]
  apply hs.congr_fun
  intro n
  have h₁ : 2 * (n : ℝ) + 5 / 2 - 107 / 100 = 2 * (143 / 200 + n) := by ring
  have h₂ : 2 * (n : ℝ) + 5 / 2 + 107 / 100 = 2 * (157 / 200 + ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    ring
  have hkcast : (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by rw [Nat.cast_add, Nat.cast_one]
  rw [h₁, h₂, mul_pow, mul_pow, hkcast]
  rw [Real.rpow_neg (show (0 : ℝ) ≤ 143 / 200 + n by positivity),
    Real.rpow_neg (show (0 : ℝ) ≤ 157 / 200 + ((n + 1 : ℕ) : ℝ) by positivity), Real.rpow_natCast,
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
theorem quarter_gamma_baseline_sum_644 :
    HasSum
      (fun n : ℕ ↦
        let c : ℝ := 2 * (n : ℝ) + 5 / 2
        2 / c - 1 / (c - 107 / 100) - 1 / (c + 107 / 100))
      ((digammaReal (143 / 200) + digammaReal (357 / 200)) / 2 - digammaReal (5 / 4)) := by
  have ha := digamma_diff_hasSum (s := 143 / 200) (t := 5 / 4) (by norm_num only) (by norm_num only)
  have hb := digamma_diff_hasSum (s := 357 / 200) (t := 5 / 4) (by norm_num only) (by norm_num only)
  have h := (ha.add hb).mul_left (1 / 2)
  have he :
    (1 / 2 : ℝ) *
        (digammaReal (143 / 200) - digammaReal (5 / 4) +
          (digammaReal (357 / 200) - digammaReal (5 / 4))) =
      (digammaReal (143 / 200) + digammaReal (357 / 200)) / 2 - digammaReal (5 / 4) := by
    ring
  rw [← he]
  apply h.congr_fun
  intro n
  dsimp only
  have h₀ : 2 * (n : ℝ) + 5 / 2 = 2 * (5 / 4 + n) := by ring
  have h₁ : 2 * (n : ℝ) + 5 / 2 - 107 / 100 = 2 * (143 / 200 + n) := by ring
  have h₂ : 2 * (n : ℝ) + 5 / 2 + 107 / 100 = 2 * (357 / 200 + n) := by ring
  rw [h₁, h₂, h₀]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The gamma baseline and the summed pole constants reduce to the two
certified digamma arguments after the forward first-pole term is removed. -/
theorem quarter_gamma_baseline_cancel_644 :
    (Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4 +
          ((digammaReal (143 / 200) + digammaReal (357 / 200)) / 2 - digammaReal (5 / 4)) -
        1 / (157 / 100) =
      (digammaReal (143 / 200) + digammaReal (157 / 200)) / 2 - Real.log Real.pi := by
  have h₁ := LLS.PaperStatements.re_digamma_real_add_one (b := 1 / 4) (by norm_num only)
  have h₂ := LLS.PaperStatements.re_digamma_real_add_one (b := 157 / 200) (by norm_num only)
  rw [show (1 / 4 : ℝ) + 1 = 5 / 4 by norm_num only] at h₁
  rw [show (157 / 200 : ℝ) + 1 = 357 / 200 by norm_num only] at h₂
  have hc : ((1 / 4 : ℝ) : ℂ) = (1 / 4 : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hc] at h₁
  unfold digammaReal
  linarith only [h₁, h₂]

/-- The normalized sum of all later pole integrals is bounded by the
summed baseline and odd coefficients, including the forward corrections. -/
theorem quarter_gamma_tail_sum_644 {y : ℝ} (hy : 0 ≤ y + 2687 / 1000) :
    let z := y + 2687 / 1000
    let A := (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z)
    let B := (digammaReal (143 / 200) + digammaReal (357 / 200)) / 2 - digammaReal (5 / 4)
    (1 / (2 * Real.pi)) * (∑' n : ℕ, ∫ t : ℝ, gammaTailTerm644 y n t) ≤
      A *
        (B * z ^ 5 + 5 * quarterGammaOdd644 1 * z ^ 4 + 10 * quarterGammaOdd644 3 * z ^ 2 +
          quarterGammaOdd644 5 +
          5 * z ^ 4 / (157 / 100) ^ 2 +
          60 * z ^ 2 / (157 / 100) ^ 4 +
          120 / (157 / 100) ^ 6) := by
  intro z A B
  have h₁ := quarter_gamma_odd_hasSum_644 (j := 1) (by decide)
  have h₃ := quarter_gamma_odd_hasSum_644 (j := 3) (by decide)
  have h₅ := quarter_gamma_odd_hasSum_644 (j := 5) (by decide)
  let p := fun n : ℕ ↦
    let c : ℝ := 2 * (n : ℝ) + 5 / 2
    let a : ℝ := 107 / 100
    let D := fun j : ℕ ↦ 1 / (c - a) ^ j - 1 / (c + a) ^ j
    A *
      ((2 / c - 1 / (c - a) - 1 / (c + a)) * z ^ 5 + 5 * D 2 * z ^ 4 + 60 * D 4 * z ^ 2 + 120 * D 6)
  have hp :=
    ((((quarter_gamma_baseline_sum_644.mul_right (z ^ 5)).add (h₁.mul_left (5 * z ^ 4))).add
              (h₃.mul_left (10 * z ^ 2))).add
          h₅).mul_left
      A
  have hps :=
    hp.congr_fun (g := p) fun n ↦ by
      dsimp only [p]
      norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd]
      ring
  have hi : Summable (fun n : ℕ ↦ ∫ t : ℝ, gammaTailTerm644 y n t) :=
    (gamma_tail_norm_summable_644 y).of_norm_bounded fun n ↦
      MeasureTheory.norm_integral_le_integral_norm _
  have hsum :=
    (hi.mul_left (1 / (2 * Real.pi))).tsum_le_tsum (fun n ↦ quarter_gamma_tail_odd_644 hy n)
      hps.summable
  rw [tsum_mul_left, hps.tsum_eq] at hsum
  convert hsum using 1
  push_cast
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.reduceAdd,
    Real.rpow_neg (by norm_num only : (0 : ℝ) ≤ 157 / 200), Real.rpow_ofNat]
  ring

/-- The central Gamma pair is at most minus 2.18 times the endpoint
weight minus the first-pole moment. Forward coefficients cancel against
the first resolvent, while the remaining coefficients use the series bound. -/
theorem quarter_gamma_pair_upper_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) (hz : 14 ≤ Real.log x + 2687 / 1000) :
    let z := Real.log x + 2687 / 1000
    let A := (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z)
    (centralGammaPair644 χ x).re ≤ -2.18 * (A * z ^ 5) - quarterGammaFirst644 z := by
  intro z A
  let y := Real.log x
  have hz₁ : 14 ≤ z := hz
  have hz₀ : 0 ≤ z := by linarith only [hz₁]
  have hz' : z ≠ 0 := ne_of_gt (by linarith only [hz₁] : 0 < z)
  have hA : 0 ≤ A := by
    dsimp only [A]; positivity
  have hs := quarter_gamma_first_split_644 χ he hx
  dsimp only at hs
  have hf := congrArg Complex.re (quarter_main_fourier_644 y)
  have hre := Complex.reCLM.integral_comp_comm (quarter_main_phase_regular_644 y).2
  change
    (∫ t : ℝ, gammaPhase644 y t) =
      (∫ t : ℝ,
          quarterKernel644.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hre
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hf
  rw [← hre,
    show -y = (2687 / 1000 : ℝ) - z by
      dsimp only [y, z]; ring,
    quarter_profile_shift_644, quarterGammaDensity644, ite_eq_left hz₀] at hf
  have hmass : (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaPhase644 y t) = A * z ^ 5 := by
    dsimp only [A]
    linarith only [hf]
  have hm :=
    congrArg (fun v : ℝ ↦ ((Complex.digamma (1 / 4 : ℂ)).re - Real.log Real.pi + 4) * v) hmass
  have hres := phase_resolvent_644 y (c := (1 / 2 : ℝ)) (by norm_num only)
  have hconv := quarter_gamma_pole_real_644 y (c := (1 / 2 : ℝ)) (by norm_num only)
  norm_num only at hres hconv
  rw [← hres, quarter_first_conv_split_644 hz₀] at hconv
  have ht := quarter_gamma_tail_sum_644 (y := y) hz₀
  have hp := mul_le_mul_of_nonneg_left (quarter_first_forward_lower_644 hz₀) hA
  have hb := quarter_gamma_baseline_cancel_644
  have hc :=
    mul_le_mul_of_nonneg_right (quarter_gamma_series_upper_644 hz)
      (mul_nonneg hA (pow_nonneg hz₀ 5))
  have h₁ : 5 * quarterGammaOdd644 1 / z * z ^ 5 = 5 * quarterGammaOdd644 1 * z ^ 4 := by
    field_simp [hz']
  have h₃ : 10 * quarterGammaOdd644 3 / z ^ 3 * z ^ 5 = 10 * quarterGammaOdd644 3 * z ^ 2 := by
    field_simp [hz']
  have h₅ : quarterGammaOdd644 5 / z ^ 5 * z ^ 5 = quarterGammaOdd644 5 :=
    div_mul_cancel₀ _ (pow_ne_zero _ hz')
  have hb' := congrArg (fun v : ℝ ↦ A * z ^ 5 * v) hb
  have h₁' := congrArg (A * ·) h₁
  have h₃' := congrArg (A * ·) h₃
  have h₅' := congrArg (A * ·) h₅
  rw [hs]
  dsimp only at ht
  dsimp only [A, z, y] at *
  nlinarith only [hm, hconv, ht, hp, hb', hc, h₁', h₃', h₅']

/-- The two original gamma contours of an even, self-inverse nonprincipal
character have the certified gamma upper bound throughout the radius interval. -/
theorem quarter_gamma_contours_rows_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hn : χ ≠ 1)
    (hi : χ⁻¹ = χ) (he : χ.Even) {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    let z := 2687 / 1000 + 2 * Real.log r
    let R := (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5
    (quarterMainArch644 χ (r ^ 2) + quarterRightGamma644 χ (r ^ 2)).re ≤ -2.18 * R - 0.02712 := by
  intro z R
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 9) (n := 27) (lo := 5755 / 1000)
        (hi := 5756 / 1000) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hlog := hl.trans (Real.log_le_log (by norm_num only) hr.1)
  have hx : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1])
  have hz : (14 : ℝ) ≤ Real.log (r ^ 2) + 2687 / 1000 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have h := quarter_gamma_pair_upper_644 χ he (zero_lt_one.trans_le hx) hz
  dsimp only at h
  rw [Real.log_pow, Nat.cast_ofNat, add_comm (2 * Real.log r)] at h
  rw [quarter_gamma_contours_central_644 χ hn hi he hx]
  exact h.trans (sub_le_sub_left (quarter_gamma_first_rows_644 hr) _)

/-- The three gamma pairs absorb the principal logarithmic allowance
`5.517 R` and leave the two recovery terms in the section 122 comparison. -/
theorem quarter_gamma_recovery_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) (hc : c ≠ 1 ∧ c⁻¹ = c ∧ c.Even)
    {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    let z := 2687 / 1000 + 2 * Real.log r
    let R := (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5
    let x := r ^ 2
    (quarterMainArch644 a x + quarterRightGamma644 a x).re +
        (quarterMainArch644 b x + quarterRightGamma644 b x).re +
        (quarterMainArch644 c x + quarterRightGamma644 c x).re +
        5.517 * R ≤
      -1.023 * R - 0.08136 := by
  dsimp only
  linarith only [quarter_gamma_contours_rows_644 a ha.1 ha.2.1 ha.2.2 hr,
    quarter_gamma_contours_rows_644 b hb.1 hb.2.1 hb.2.2 hr,
    quarter_gamma_contours_rows_644 c hc.1 hc.2.1 hc.2.2 hr]

/-- The endpoint factor in the gamma calculation is the physical weight
at one used by the adjusted principal gap. -/
theorem quarter_weight_one_644 (r : ℝ) :
    let z := 2687 / 1000 + 2 * Real.log r
    quarterWeight644 (r ^ 2) 1 =
      (107 / 100 : ℝ) ^ 5 / 120 * Real.exp (-(107 / 100) * z) * z ^ 5 := by
  intro z
  unfold quarterWeight644
  simp only [Real.sqrt_one, div_one, one_mul, one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  have he : -((107 / 100 : ℝ) * (2687 / 1000 - -(2 * Real.log r))) = -(107 / 100) * z := by
    dsimp only [z]; ring
  rw [he]
  dsimp only [z]
  ring

/-- The actual principal logarithmic allowance is absorbed by the three
gamma contours using the same endpoint weight as the adjusted principal gap. -/
theorem quarter_gamma_adjusted_recovery_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ s}
    (ha : a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b ≠ 1 ∧ b⁻¹ = b ∧ b.Even) (hc : c ≠ 1 ∧ c⁻¹ = c ∧ c.Even)
    {r : ℝ} (hr : r ∈ Set.Icc 316 322) :
    let x := r ^ 2
    let R := quarterWeight644 x 1
    (quarterMainArch644 a x + quarterRightGamma644 a x).re +
        (quarterMainArch644 b x + quarterRightGamma644 b x).re +
        (quarterMainArch644 c x + quarterRightGamma644 c x).re +
        3 * Real.log (2 * Real.pi) * R ≤
      -1.023 * R - 0.08136 := by
  intro x R
  have hw := quarter_weight_one_644 r
  dsimp only at hw
  have hz : 0 ≤ 2687 / 1000 + 2 * Real.log r := by
    linarith only [Real.log_nonneg (show 1 ≤ r by linarith only [hr.1])]
  have hR : 0 ≤ R := by
    change 0 ≤ quarterWeight644 (r ^ 2) 1
    rw [hw]
    positivity
  have hlog :=
    mul_le_mul_of_nonneg_right
      (show 3 * Real.log (2 * Real.pi) ≤ 5.517 by linarith only [Analysis.log_two_mul_pi_lt]) hR
  have h := quarter_gamma_recovery_644 ha hb hc hr
  dsimp only at h
  rw [← hw] at h
  dsimp only [R, x] at hlog ⊢
  linarith only [hlog, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
