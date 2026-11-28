/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPole570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaTailSeries

/-! # Signed Gamma tail and section 31 character contradiction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The second height moment of the sixth-pole kernel is integrable. Scale
the difference of the integrable second and third Cauchy powers. -/
theorem second_integrable_570 :
    MeasureTheory.Integrable (fun t : ℝ ↦ t ^ 2 * ‖quarterKernel570.function (Complex.I * t)‖) := by
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
              (by norm_num only : (50 / 51 : ℝ) ≠ 0)).mpr
          hn).const_mul
      (51 / 50 : ℝ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [quarter_zero_norm_570]
  have h1 : (51 / 50 : ℝ) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h2 : 1 + ((50 / 51 : ℝ) * t) ^ 2 ≠ 0 := by positivity
  field_simp

/-- The actual phase divided by the first-pole denominator is integrable.
The reciprocal denominator is continuous and bounded by four. -/
theorem resolvent_integrable_570 (y : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase570 y t / (1 / 4 + t ^ 2)) := by
  have hden (t : ℝ) : 1 / 4 + t ^ 2 ≠ (0 : ℝ) := by nlinarith only [sq_nonneg t]
  have hc : Continuous (fun t : ℝ ↦ (1 / 4 + t ^ 2)⁻¹) := by
    exact (continuous_const.add (continuous_id.pow 2)).inv₀ hden
  have hi := (gamma_phase_integrable_570 y).2.1
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

private theorem mass_nonneg_570 (y : ℝ) : 0 ≤ ∫ t : ℝ, gammaPhase570 y t := by
  have h := phase_mass_eq_density_570 y
  have hd : 0 ≤ gammaDensity570 (y + 14 / 5) := by
    unfold gammaDensity570
    split_ifs with hv
    · positivity
    · exact le_rfl
  exact nonneg_of_mul_nonneg_right (h.symm ▸ hd) (by positivity : 0 < 1 / (2 * Real.pi))

/-- The term after the first pole in the even digamma correction, multiplied by the
real oscillatory phase. Its index starts at the pole with rate `5/2`. -/
noncomputable def gammaTailTerm570 (y : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ((t / 2) ^ 2 / ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2))) *
    gammaPhase570 y t

/-- Each signed tail term is absolutely bounded by the second kernel moment times
the corresponding inverse cube. This is the majorant for termwise integration. -/
theorem gamma_tail_term_bound_570 (y : ℝ) (n : ℕ) (t : ℝ) :
    ‖gammaTailTerm570 y n t‖ ≤
      (2 / (2 * (n : ℝ) + 5 / 2) ^ 3) * (t ^ 2 * ‖quarterKernel570.function (Complex.I * t)‖) := by
  have ha : 0 < (1 / 4 : ℝ) + ((n + 1 : ℕ) : ℝ) := by positivity
  have hd :
    0 ≤
      (t / 2) ^ 2 /
        ((1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2)) :=
    div_nonneg (sq_nonneg _) (mul_nonneg ha.le (add_nonneg (sq_nonneg _) (sq_nonneg _)))
  have hp : |gammaPhase570 y t| ≤ ‖quarterKernel570.function (Complex.I * t)‖ := by
    have h :=
      Complex.abs_re_le_norm
        (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y))
    rw [norm_mul, Complex.norm_exp] at h
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero, mul_one] at h
    exact h
  rw [gammaTailTerm570, norm_mul, Real.norm_eq_abs, abs_of_nonneg hd, Real.norm_eq_abs]
  have h :=
    mul_le_mul (target028_gamma_correction_term t n) hp (abs_nonneg _)
      (le_trans hd (target028_gamma_correction_term t n))
  convert h using 1
  ring

/-- Each tail term is integrable: its continuous integrand is dominated by the
integrable second moment of the sixth-pole kernel. -/
theorem gamma_tail_term_integrable_570 (y : ℝ) (n : ℕ) :
    MeasureTheory.Integrable (gammaTailTerm570 y n) := by
  have hd (t : ℝ) :
    (1 / 4 + ((n + 1 : ℕ) : ℝ)) * ((1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 + (t / 2) ^ 2) ≠ 0 := by
    positivity
  have hc : Continuous (gammaTailTerm570 y n) := by
    unfold gammaTailTerm570
    apply Continuous.mul
    · exact
        ((continuous_id.div_const 2).pow 2).div
          (continuous_const.mul (continuous_const.add ((continuous_id.div_const 2).pow 2))) hd
    · exact (gamma_phase_integrable_570 y).1
  apply
    (second_integrable_570.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (gamma_tail_term_bound_570 y n)

/-- The integrals of the absolute tail terms form a convergent series, using the
summable inverse-cube bound for the pole rates. -/
theorem gamma_tail_norm_summable_570 (y : ℝ) :
    Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖gammaTailTerm570 y n t‖) := by
  let C : ℝ := ∫ t : ℝ, t ^ 2 * ‖quarterKernel570.function (Complex.I * t)‖
  have hs : Summable (fun n : ℕ ↦ (2 * C) * (1 / (2 * (n : ℝ) + 5 / 2) ^ 3)) :=
    target028_gamma_pole_tail_summable.mul_left (2 * C)
  apply hs.of_nonneg_of_le
  · intro n
    exact MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _)
  · intro n
    have hi := gamma_tail_term_integrable_570 y n
    have hmajor := second_integrable_570.const_mul (2 / (2 * (n : ℝ) + 5 / 2) ^ 3)
    have h := MeasureTheory.integral_mono hi.norm hmajor (gamma_tail_term_bound_570 y n)
    rw [MeasureTheory.integral_const_mul] at h
    dsimp only [C]
    convert h using 1
    ring

/-- The oscillatory even-Gamma tail can be integrated term by term: the individual
terms are integrable and their integral norms form a summable series. -/
theorem gamma_tail_integral_tsum_570 (y : ℝ) :
    (∫ t : ℝ, ∑' n : ℕ, gammaTailTerm570 y n t) = ∑' n : ℕ, ∫ t : ℝ, gammaTailTerm570 y n t := by
  exact
    (MeasureTheory.integral_tsum_of_summable_integral_norm (gamma_tail_term_integrable_570 y)
        (gamma_tail_norm_summable_570 y)).symm

/-- Above the shifted scale thirteen, the integral of each even-Gamma correction
after the first pole is nonpositive. The phase mass and resolvent are paired before
integration, avoiding a difference of divergent series. -/
theorem gamma_tail_term_integral_nonpos_570 {y : ℝ} (hy : 13 ≤ y + 14 / 5) (n : ℕ) :
    (∫ t : ℝ, gammaTailTerm570 y n t) ≤ 0 := by
  let c : ℝ := 2 * (n : ℝ) + 5 / 2
  have hc : (5 / 2 : ℝ) ≤ c := by
    dsimp only [c]; linarith only [Nat.cast_nonneg (α := ℝ) n]
  have hc0 : 0 < c := by linarith only [hc]
  have hden (t : ℝ) : c ^ 2 + t ^ 2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc0) (sq_nonneg t)).ne'
  have he (t : ℝ) :
    gammaTailTerm570 y n t =
      (2 / c) * (gammaPhase570 y t - c ^ 2 * (gammaPhase570 y t / (c ^ 2 + t ^ 2))) := by
    dsimp only [gammaTailTerm570, c]
    push_cast
    field_simp
    ring
  have hr (t : ℝ) :
    gammaPhase570 y t / (c ^ 2 + t ^ 2) =
      (c ^ 2)⁻¹ * (gammaPhase570 y t - (c / 2) * gammaTailTerm570 y n t) := by
    rw [he]
    field_simp
    ring
  have hiP := (gamma_phase_integrable_570 y).2.1
  have hiF := gamma_tail_term_integrable_570 y n
  have hiR : MeasureTheory.Integrable (fun t : ℝ ↦ gammaPhase570 y t / (c ^ 2 + t ^ 2)) := by
    apply ((hiP.sub (hiF.const_mul (c / 2))).const_mul (c ^ 2)⁻¹).congr
    exact Filter.Eventually.of_forall (fun t ↦ (hr t).symm)
  have hint :
    (∫ t : ℝ, gammaTailTerm570 y n t) =
      (2 / c) *
        ((∫ t : ℝ, gammaPhase570 y t) - c ^ 2 * ∫ t : ℝ, gammaPhase570 y t / (c ^ 2 + t ^ 2)) := by
    have hfun :
      gammaTailTerm570 y n = fun t ↦
        (2 / c) * (gammaPhase570 y t - c ^ 2 * (gammaPhase570 y t / (c ^ 2 + t ^ 2))) :=
      funext he
    rw [hfun, MeasureTheory.integral_const_mul, MeasureTheory.integral_sub hiP (hiR.const_mul _),
      MeasureTheory.integral_const_mul]
  have hcmp := phase_mass_le_resolvent_570 hy hc
  rw [hint]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.mpr hcmp)

/-- Above the shifted scale thirteen, the integrated even-Gamma tail after the
first pole is nonpositive. Absolute convergence permits termwise integration. -/
theorem gamma_tail_integral_nonpos_570 {y : ℝ} (hy : 13 ≤ y + 14 / 5) :
    (∫ t : ℝ, ∑' n : ℕ, gammaTailTerm570 y n t) ≤ 0 := by
  rw [gamma_tail_integral_tsum_570]
  exact tsum_nonpos (gamma_tail_term_integral_nonpos_570 hy)

/-- The oscillatory digamma increment after removing its first pole equals the
convergent series of signed tail terms. The identity separates the first term of
the vertical digamma expansion and distributes the phase over the remaining sum. -/
theorem gamma_tail_eq_series_570 (y t : ℝ) :
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        gammaPhase570 y t =
      ∑' n : ℕ, gammaTailTerm570 y n t := by
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
  simp only [gammaTailTerm570, tsum_mul_right]
  have he := congrArg (fun x : ℝ ↦ (x - (4 - 1 / (1 / 4 + t ^ 2))) * gammaPhase570 y t) h
  simpa only [add_sub_cancel_left, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] using he

/-- At shifted scale at least twelve, the integrated vertical digamma correction
after its first pole is nonpositive. This combines the pointwise series identity
with the absolute convergence and polewise sign estimates. -/
theorem gamma_tail_signed_570 {y : ℝ} (hy : 13 ≤ y + 14 / 5) :
    (∫ t : ℝ,
        ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
            (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
            (4 - 1 / (1 / 4 + t ^ 2))) *
          gammaPhase570 y t) ≤
      0 := by
  simpa only [gamma_tail_eq_series_570] using gamma_tail_integral_nonpos_570 hy

/-- Above shifted scale thirteen, the even-Gamma phase integral and first-pole
resolvent retain the negative baseline. The baseline is at most negative four
thirds times the nonnegative phase mass, and the remaining tail is nonpositive. -/
theorem gamma_phase_baseline_570 {y : ℝ} (hy : 13 ≤ y + 14 / 5)
    (hG :
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            gammaPhase570 y t)) :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            gammaPhase570 y t) +
        (∫ t : ℝ, gammaPhase570 y t / (1 / 4 + t ^ 2)) ≤
      -(4 / 3 : ℝ) * (∫ t : ℝ, gammaPhase570 y t) := by
  let B : ℝ := (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re - Real.log Real.pi
  let P := gammaPhase570 y
  let E : ℝ → ℝ := fun t ↦
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t -
        (B + 4) * P t +
      P t / (1 / 4 + t ^ 2)
  have hP : MeasureTheory.Integrable P := (gamma_phase_integrable_570 y).2.1
  have hR : MeasureTheory.Integrable (fun t ↦ P t / (1 / 4 + t ^ 2)) := resolvent_integrable_570 y
  have he (t : ℝ) :
    E t =
      ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
          (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
          (4 - 1 / (1 / 4 + t ^ 2))) *
        P t := by
    dsimp only [E, B]
    ring
  have hneg : (∫ t : ℝ, E t) ≤ 0 := by simpa only [he, P] using gamma_tail_signed_570 hy
  have hbase : B + 4 ≤ -(4 / 3 : ℝ) := by
    dsimp only [B]
    linarith only [LLS.PaperStatements.gamma_even_baseline_lt]
  have hmass := mass_nonneg_570 y
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

/-- Above shifted scale thirteen, the even-Gamma phase integral and the first-pole
resolvent have a nonpositive sum. The negative baseline and signed tail provide
the estimate. -/
theorem gamma_phase_negative_570 {y : ℝ} (hy : 13 ≤ y + 14 / 5)
    (hG :
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            gammaPhase570 y t)) :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
            gammaPhase570 y t) +
        (∫ t : ℝ, gammaPhase570 y t / (1 / 4 + t ^ 2)) ≤
      0 := by
  have h := gamma_phase_baseline_570 hy hG
  have hm := mass_nonneg_570 y
  have hn : -(4 / 3 : ℝ) * (∫ t : ℝ, gammaPhase570 y t) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hm
  exact h.trans hn

/-- The first resolvent integral is nonnegative at every scale, since its
positive-half-line convolution has a nonnegative density. -/
theorem first_resolvent_nonneg_570 (y : ℝ) : 0 ≤ ∫ t : ℝ, gammaPhase570 y t / (1 / 4 + t ^ 2) := by
  have h := congrArg Complex.re (pole_density_positive_570 y (by norm_num only : (0 : ℝ) < 1 / 2))
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [← phase_resolvent_570 y (by norm_num only : (0 : ℝ) < 1 / 2)] at h
  have hd (v : ℝ) : 0 ≤ gammaDensity570 v := by
    unfold gammaDensity570
    split_ifs with hv
    · positivity
    · exact le_rfl
  have hi :
    0 ≤ ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - (y + 14 / 5)|) :=
    MeasureTheory.integral_nonneg (fun v ↦ mul_nonneg (hd v) (Real.exp_pos _).le)
  norm_num only at h
  exact nonneg_of_mul_nonneg_right (h.symm ▸ mul_nonneg (by norm_num only) hi) (by positivity)

/-- At shifted logarithms at least thirteen, the even Gamma contribution saves
both four thirds of the shifted density and the first resolvent convolution.
The pole identity turns the normalized resolvent into a positive real integral. -/
theorem central_gamma_convolution_upper {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q)
    (ea : a.Even) {x : ℝ} (hx : 0 < x) (hy : 13 ≤ Real.log x + 14 / 5) :
    (centralGammaPair570 a x).re ≤
      -(4 / 3 : ℝ) * gammaDensity570 (Real.log x + 14 / 5) -
        ∫ v in Set.Ioi (0 : ℝ),
          gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log x + 14 / 5)|) := by
  let y := Real.log x
  obtain ⟨hi, he⟩ := central_real_phase_570 a ea hx
  have hb := gamma_phase_baseline_570 hy hi
  have hm := phase_mass_eq_density_570 y
  have hr := congrArg Complex.re (pole_density_positive_570 y (by norm_num only : (0 : ℝ) < 1 / 2))
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hr
  rw [← phase_resolvent_570 y (by norm_num only : (0 : ℝ) < 1 / 2)] at hr
  norm_num only at hr
  rw [he, div_eq_inv_mul]
  dsimp only [y] at hm hr
  rw [← hm]
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2 * Real.pi)⁻¹ by positivity)
  simp only [one_div] at hr ⊢
  linarith only [hb', hr]

/-- For an even character the section 31 Gamma integral has nonpositive real
part whenever the shifted logarithm is at least thirteen. Sum the signed tail
and drop the nonnegative first resolvent. -/
theorem central_gamma_nonpos_570 {q : ℕ} [NeZero q] (a : DirichletCharacter ℂ q) (ea : a.Even)
    {x : ℝ} (hx : 0 < x) (hy : 13 ≤ Real.log x + 14 / 5) : (centralGammaPair570 a x).re ≤ 0 := by
  obtain ⟨hi, he⟩ := central_real_phase_570 a ea hx
  have hn := gamma_phase_negative_570 hy hi
  have hp := first_resolvent_nonneg_570 (Real.log x)
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  linarith only [hn, hp]

/-- On the full section 31 interval three primitive even characters with the stated trace
and conductor bounds cannot simultaneously equal one on every prime up to the cutoff.
The lower contour comparison and the signed Gamma upper bound contradict each other. -/
theorem triple_impossible_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) : False := by
  have hp :=
    central_gamma_positive_570 hG a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB hC hlog
      ea eb ec
  have hr : 0 < r := by linarith only [hl]
  have ht' :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 16) (lo := 56 / 10) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at ht'
  have hlogr := ht'.trans (Real.log_le_log (by norm_num only) hl)
  have hy : 13 ≤ Real.log (r ^ 2) + 14 / 5 := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [hlogr]
  have hn := central_gamma_nonpos_570 a ea (sq_pos_of_pos hr) hy
  linarith only [hp, hn]

end PseudoPrime.PrimeTestBounds.MillerRabin
