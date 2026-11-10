/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution

/-! # A one-sided even-Gamma integral estimate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The one-sided Gamma estimate retains the first-pole resolvent integral.
The baseline has nonpositive mass, while the remaining digamma tail is
controlled by the second moment. -/
theorem quarter_gamma_phase_with_pole (P : ℝ → ℝ) (hP : MeasureTheory.Integrable P)
    (hR : MeasureTheory.Integrable (fun t ↦ P t / (1 / 4 + t ^ 2)))
    (hG :
      MeasureTheory.Integrable
        (fun t ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t))
    (hPint : 0 ≤ ∫ t : ℝ, P t)
    (hPk : ∀ t : ℝ, P t ≤ ‖refinedSixPoleKernel.function (Complex.I * t)‖) :
    ((∫ t : ℝ,
            ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) *
              P t) +
          ∫ t : ℝ, P t / (1 / 4 + t ^ 2)) /
        (2 * Real.pi) ≤
      (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  let B : ℝ := (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re - Real.log Real.pi
  let E : ℝ → ℝ := fun t ↦
    ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t -
        (B + 4) * P t +
      P t / (1 / 4 + t ^ 2)
  have hEi : MeasureTheory.Integrable E := (hG.sub (hP.const_mul (B + 4))).add hR
  have hbound (t : ℝ) :
    E t ≤ (26 / 125 : ℝ) * (t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖) := by
    let d : ℝ :=
      (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re -
        (Complex.digamma ((1 / 4 : ℝ) : ℂ)).re -
        (4 - 1 / (1 / 4 + t ^ 2))
    have hd0 : 0 ≤ d := by
      dsimp only [d]
      linarith only [target028_gamma_vertical_lower t]
    have hd : d ≤ (26 / 125 : ℝ) * t ^ 2 := by
      dsimp only [d]
      linarith only [target028_gamma_vertical_upper t]
    have hm := mul_le_mul_of_nonneg_left (hPk t) hd0
    have hn :=
      mul_le_mul_of_nonneg_right hd (norm_nonneg (refinedSixPoleKernel.function (Complex.I * t)))
    have he : E t = d * P t := by
      dsimp only [E, d, B]
      ring
    rw [he]
    nlinarith only [hm, hn]
  have hmain := target028_gamma_tail_integral_bound E hEi hbound
  have hbase : B + 4 ≤ 0 := by
    dsimp only [B]
    linarith only [target028_gamma_baseline]
  have hneg := mul_nonpos_of_nonpos_of_nonneg hbase hPint
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
  have hle :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) +
        (∫ t : ℝ, P t / (1 / 4 + t ^ 2)) ≤
      ∫ t : ℝ, E t := by
    linarith only [heint, hneg]
  exact (div_le_div_of_nonneg_right hle (mul_nonneg (by norm_num only) Real.pi_pos.le)).trans hmain

/-- A real kernel phase with nonnegative total mass and first-pole resolvent
has a small one-sided even-Gamma integral. The baseline cancels the first-pole
constant; the remaining nonnegative tail is controlled by the second moment.
The integrability and sign hypotheses are supplied by inverse Mellin inversion. -/
theorem target028_gamma_one_sided_of_phase (P : ℝ → ℝ) (hP : MeasureTheory.Integrable P)
    (hR : MeasureTheory.Integrable (fun t ↦ P t / (1 / 4 + t ^ 2)))
    (hG :
      MeasureTheory.Integrable
        (fun t ↦
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t))
    (hPint : 0 ≤ ∫ t : ℝ, P t) (hRint : 0 ≤ ∫ t : ℝ, P t / (1 / 4 + t ^ 2))
    (hPk : ∀ t : ℝ, P t ≤ ‖refinedSixPoleKernel.function (Complex.I * t)‖) :
    (∫ t : ℝ,
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi) * P t) /
        (2 * Real.pi) ≤
      (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  have h := quarter_gamma_phase_with_pole P hP hR hG hPint hPk
  have hp : 0 ≤ (∫ t : ℝ, P t / (1 / 4 + t ^ 2)) / (2 * Real.pi) :=
    div_nonneg hRint (mul_nonneg (by norm_num only) Real.pi_pos.le)
  rw [add_div] at h
  linarith only [h, hp]

/-- The real oscillatory phase of the sixth-pole kernel at logarithmic scale
`y`. Its integral is the nonnegative inverse-Mellin profile. -/
noncomputable def target028GammaPhase (y t : ℝ) : ℝ :=
  (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)).re

/-- The actual sixth-pole phase is continuous and integrable at every real
logarithmic scale. The exponential phase has unit modulus, so the kernel's
existing line-integrability estimate supplies the bound. -/
theorem target028_gamma_phase_integrable (y : ℝ) :
    Continuous (target028GammaPhase y) ∧
      MeasureTheory.Integrable (target028GammaPhase y) ∧
      MeasureTheory.Integrable
        (fun t : ℝ ↦
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)) := by
  have hp : Continuous (fun t : ℝ ↦ Complex.exp (Complex.I * (t : ℂ) * y)) :=
    Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  have hc := target028_kernel_line_continuous.mul hp
  have hk :=
    LLS.PaperStatements.MellinKernel.integrable_line refinedSixPoleKernel (c := 0)
      (by norm_num only) (by linarith only [refinedSixPoleKernel.delta_pos])
  have hk' :
    MeasureTheory.Integrable (fun t : ℝ ↦ refinedSixPoleKernel.function (Complex.I * t)) := by
    simpa only [Complex.ofReal_zero, zero_add] using hk
  have hi :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) := by
    apply hk'.mul_bdd (c := 1) hp.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_exp]
    have hre : (Complex.I * (t : ℂ) * y).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    rw [hre, Real.exp_zero]
  exact ⟨Complex.continuous_re.comp hc, hi.re, hi⟩

/-- The actual phase divided by the first-pole denominator is integrable.
The reciprocal denominator is continuous and bounded by four. -/
theorem target028_gamma_resolvent_integrable (y : ℝ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ target028GammaPhase y t / (1 / 4 + t ^ 2)) := by
  have hden (t : ℝ) : 1 / 4 + t ^ 2 ≠ (0 : ℝ) := by nlinarith only [sq_nonneg t]
  have hc : Continuous (fun t : ℝ ↦ (1 / 4 + t ^ 2)⁻¹) := by
    exact (continuous_const.add (continuous_id.pow 2)).inv₀ hden
  have hi := (target028_gamma_phase_integrable y).2.1
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

/-- The integral of the actual oscillatory phase is nonnegative by inverse
Mellin inversion of the nonnegative sixth-pole profile. -/
theorem target028_gamma_phase_mass_nonneg (y : ℝ) : 0 ≤ ∫ t : ℝ, target028GammaPhase y t := by
  have hi := (target028_gamma_phase_integrable y).2.2
  have hr := Complex.reCLM.integral_comp_comm hi
  change
    (∫ t : ℝ, target028GammaPhase y t) =
      (∫ t : ℝ,
          refinedSixPoleKernel.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hr
  rw [hr]
  exact target028_kernel_fourier_nonneg y

/-- The first-pole integral of the real phase equals the real part of the
complex resolvent integral. The bounded resolvent gives integrability, so
the continuous real-part map commutes with integration. -/
theorem quarter_phase_resolvent_eq (y : ℝ) :
    (∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2)) =
      (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (1 / 4 + t ^ 2) : ℝ) : ℂ)).re := by
  have hden (t : ℝ) : 0 < 1 / 4 + t ^ 2 := by nlinarith only [sq_nonneg t]
  have hc : Continuous (fun t : ℝ ↦ (((1 / 4 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t ↦ (hden t).ne'))
  have hi := (target028_gamma_phase_integrable y).2.2
  have hm := hi.mul_bdd (c := 4) hc.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(((1 / 4 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (4 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hden t).le), ← one_div]
    apply (div_le_iff₀ (hden t)).2
    nlinarith only [sq_nonneg t]
  have hr := Complex.reCLM.integral_comp_comm (hm hb)
  change
    (∫ t : ℝ,
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((1 / 4 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) =
      _ at hr
  have he :
    (∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2)) =
      (∫ t : ℝ,
        (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((1 / 4 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [target028GammaPhase, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  rw [he, hr]
  simp only [one_div]
  rfl

/-- The first-pole resolvent integral of the actual real phase is nonnegative.
The complex statement follows from the positive Laplace convolution. -/
theorem target028_gamma_resolvent_mass_nonneg (y : ℝ) :
    0 ≤ ∫ t : ℝ, target028GammaPhase y t / (1 / 4 + t ^ 2) := by
  rw [quarter_phase_resolvent_eq]
  simpa only [one_div] using target028_first_pole_kernel_nonneg y

/-- The even central Gamma integral and its normalized first-pole phase
integral satisfy the one-sided second-moment bound. This retains the pole
contribution for sharper bounds on a specified scale range. -/
theorem quarter_gamma_central_with_pole {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    (refinedCentralGammaPair χ x).re +
        (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) ≤
      (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
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
  have hPk (t : ℝ) : P t ≤ ‖refinedSixPoleKernel.function (Complex.I * t)‖ := by
    dsimp only [P, target028GammaPhase]
    have h :=
      Complex.re_le_norm
        (refinedSixPoleKernel.function (Complex.I * t) *
          Complex.exp (Complex.I * (t : ℂ) * Real.log x))
    rw [norm_mul, Complex.norm_exp] at h
    have hre : (Complex.I * (t : ℂ) * Real.log x).re = 0 := by
      simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, one_mul, zero_add]
    simpa only [hre, Real.exp_zero, mul_one] using h
  have hb :=
    quarter_gamma_phase_with_pole P (target028_gamma_phase_integrable _).2.1
      (target028_gamma_resolvent_integrable _) hG (target028_gamma_phase_mass_nonneg _) hPk
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
  rw [add_div, ← hpair] at hb
  exact hb

/-- The paired even central Gamma integral has the sharp uniform one-sided
bound `13(27/25)^2/1000`. Inverse Mellin inversion supplies the two positive
phase integrals, and the second moment controls the remaining digamma tail. -/
theorem target028_central_gamma_pair_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    (refinedCentralGammaPair χ x).re ≤ (13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  have h := quarter_gamma_central_with_pole χ he hx
  have hp : 0 ≤ (∫ t : ℝ, target028GammaPhase (Real.log x) t / (1 / 4 + t ^ 2)) / (2 * Real.pi) :=
    div_nonneg (target028_gamma_resolvent_mass_nonneg (Real.log x))
      (mul_nonneg (by norm_num only) Real.pi_pos.le)
  linarith only [h, hp]

/-- Three common even Gamma terms fit the explicit scaled budget `21/50`.
The stronger bound from the second moment is compared by rational arithmetic. -/
theorem target028_three_gamma_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    3 * (refinedCentralGammaPair χ x).re < (21 / 50 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h := target028_central_gamma_pair_le χ he hx
  have hc : 3 * ((13 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 2) < (21 / 50 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
    norm_num only
  linarith only [h, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
