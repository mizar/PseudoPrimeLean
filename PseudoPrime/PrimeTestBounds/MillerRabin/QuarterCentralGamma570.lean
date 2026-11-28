/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContourGap570
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaContour

/-! # Central Gamma contour for the section 31 kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem kernel_function_570 (z : ℂ) :
    quarterKernel570.function z =
      ((51 / 50 : ℂ) ^ 5) * (Complex.exp ((14 / 5 : ℂ) * z) / (z + 51 / 50) ^ 6) := by
  change Analysis.rationalPoleFunction 3 (25 / 51) (7 / 5) z = _
  rw [Analysis.rationalPole_eq_shifted_power 3 (by norm_num only) (7 / 5) z]
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Nat.reduceMul]

/-- On every vertical line between the center and `9/16`, the Gamma-factor
integrand is absolutely integrable. The admissible Mellin-kernel estimate
controls the logarithmic Gamma growth. -/
theorem gamma_line_integrable_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) (hc' : c ≤ 9 / 16) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (quarterKernel570.function ((c : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hi :=
    LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line quarterKernel570 χ (c := c)
      (x := x) (by linarith only [hc])
      (by
        rw [hd]; linarith only [hc'])
      (by linarith only [hc']) hx
  simpa only [mul_assoc] using hi

/-- The Gamma-factor logarithmic derivative weighted by the refined kernel
and the positive scale power. Its vertical integrals form the Gamma contour cost. -/
noncomputable def gammaIntegrand570 {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv χ.gammaFactor (s + 1 / 2) * (quarterKernel570.function s * (x : ℂ) ^ s)

/-- The actual right Gamma contour equals its central-line integral at every
positive scale. The general positive-scale Gamma contour theorem supplies the
horizontal decay and the line shift for the sixth-pole Mellin kernel. -/
theorem right_gamma_eq_central_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    rightGamma570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)) := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central_of_pos quarterKernel570 χ (b :=
      9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx
  unfold rightGamma570
  rw [h]
  apply congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  simp only [gammaIntegrand570, zero_add, mul_comm Complex.I]

/-- On every vertical line from `-9/16` to zero, the reflected Gamma-factor
integrand is absolutely integrable. Gamma's logarithmic growth is absorbed by
the admissible Mellin-kernel decay. -/
theorem reflected_gamma_line_integrable_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 0) (hcne : c ≠ -1 / 2) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) *
          (quarterKernel570.function ((c : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hσ : 0 < 1 / 2 - c := by linarith only [hc']
  have hσ2 : 1 / 2 - c ≤ 2 := by linarith only [hc]
  obtain ⟨A, hA, hb⟩ := AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_vertical_log χ hσ hσ2
  have hF :
    Continuous
      (fun t : ℝ ↦ logDeriv χ.gammaFactor (((1 / 2 - c : ℝ) : ℂ) + Complex.I * (-t : ℝ))) :=
    (AnalyticNumberTheory.DirichletLFunction.continuous_gammaLogDeriv_vertical χ hσ).comp
      continuous_neg
  have he (t : ℝ) :
    (1 / 2 : ℂ) - ((c : ℂ) + Complex.I * t) = (((1 / 2 - c : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
    push_cast; ring
  have hi :=
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line quarterKernel570 (c := c)
      (x := x) (F := fun t ↦ logDeriv χ.gammaFactor (((1 / 2 - c : ℝ) : ℂ) + Complex.I * (-t : ℝ)))
      (A := A)
      (by
        rw [hd]; linarith only [hc])
      (by
        rw [hd]; linarith only [hc'])
      hcne hx hF.aestronglyMeasurable (fun t ↦ by simpa only [abs_neg] using hb (-t))
  simpa only [he, mul_assoc] using hi

/-- For scale at least one, the reflected Gamma contour has vanishing
horizontal edges at signed heights tending to infinity. Gamma has logarithmic
growth and the admissible kernel supplies quadratic decay. -/
theorem reflected_gamma_horizontal_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ σ in (-(9 / 16 : ℝ))..(0 : ℝ),
          logDeriv χ.gammaFactor (1 / 2 - ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) *
            quarterKernel570.function ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  let G : ℝ :=
    ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + AnalyticNumberTheory.Gamma.digammaLogErrorBound + 4
  let D := |G| + Real.log 5 + 1
  have ht (n : ℕ) : 1 ≤ T n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have heabs (n : ℕ) : |e * T n| = T n := by
    rcases he with rfl | rfl
    · rw [one_mul, abs_of_nonneg (zero_lt_one.trans_le (ht n)).le]
    · rw [neg_one_mul, abs_neg, abs_of_nonneg (zero_lt_one.trans_le (ht n)).le]
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num only))) zero_le_one
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  apply
    LLS.PaperStatements.MellinKernel.tendsto_horizontalIntegral_of_scaled_bound quarterKernel570
      (a := -(9 / 16 : ℝ)) (b := 0) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      hx (fun n ↦ e * T n) (fun n ↦ (Real.log (T n) + D) / (T n) ^ 2)
      (fun n ↦ by
        rw [heabs]; exact ht n)
      (fun n ↦ div_nonneg (add_nonneg (Real.log_nonneg (ht n)) hD) (sq_nonneg _))
      (AnalyticNumberTheory.General.tendsto_log_add_const_div_sq_atTop D |>.comp hT)
      (fun s : ℂ ↦ logDeriv χ.gammaFactor (1 / 2 - s))
  intro n σ hσ
  have hσ' : -(9 / 16 : ℝ) < σ ∧ σ ≤ 0 := by
    simpa only [Set.uIoc_of_le (by norm_num only : -(9 / 16 : ℝ) ≤ 0), Set.mem_Ioc] using hσ
  have hsr : |((1 / 2 : ℂ) - ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I)).re| ≤ 2 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    exact abs_le.mpr ⟨by linarith only [hσ'.2], by linarith only [hσ'.1]⟩
  have hsi : ((1 / 2 : ℂ) - ((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I)).im = -(e * T n) := by
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.div_ofNat_im,
      Complex.one_im, zero_div, zero_sub]
  have hg :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_le_log χ hsr
      (by
        rw [hsi, abs_neg, heabs]; exact ht n)
  rw [hsi, abs_neg, heabs] at hg
  have hl := AnalyticNumberTheory.General.log_four_add_le_log_add_log_five (ht n)
  have hn : 0 ≤ Real.log (T n) := Real.log_nonneg (ht n)
  have hsquare : (e * T n) ^ 2 = (T n) ^ 2 := by
    rcases he with rfl | rfl
    · rw [one_mul]
    · rw [neg_one_mul, neg_sq]
  rw [hsquare, div_mul_cancel₀ _ (sq_pos_of_pos (zero_lt_one.trans_le (ht n))).ne']
  dsimp only [D, G]
  have hGa : G ≤ |G| := le_abs_self G
  dsimp only [G] at hGa
  have h5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num only)
  nlinarith only [hg, hl, hn, hGa, abs_nonneg G, h5]

/-- The reflected Gamma-factor integrand used on the negative contour. -/
noncomputable def reflectedGammaIntegrand570 {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) :
    ℂ :=
  logDeriv χ.gammaFactor (1 / 2 - s) * (quarterKernel570.function s * (x : ℂ) ^ s)

/-- The reflected Gamma integrand is differentiable between the left contour
and the central line. Both the Gamma argument and the distance from the kernel
pole have positive real part there. -/
theorem reflected_gamma_differentiable_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) {z : ℂ} (hz : -(9 / 16 : ℝ) ≤ z.re) (hz' : z.re ≤ 0) :
    DifferentiableAt ℂ (reflectedGammaIntegrand570 χ x) z := by
  have hh : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by
    push_cast; ring
  have hpos : 0 < ((1 / 2 : ℂ) - z).re := by
    rw [hh, Complex.sub_re, Complex.ofReal_re]
    linarith only [hz']
  have ha := AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ hpos
  have hn := AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hpos
  have hg : DifferentiableAt ℂ (fun s : ℂ ↦ logDeriv χ.gammaFactor (1 / 2 - s)) z :=
    (ha.deriv.div ha hn).differentiableAt.comp z
      (differentiableAt_const _ |>.sub differentiableAt_id)
  have hden : z + (51 / 50 : ℂ) ≠ 0 := by
    intro h
    have h27 : (51 / 50 : ℂ) = (((51 / 50 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h27] at h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith only [hz, h']
  have hk : DifferentiableAt ℂ quarterKernel570.function z := by
    have he :
      quarterKernel570.function = fun s : ℂ ↦
        ((51 / 50 : ℂ) ^ 5) * (Complex.exp ((14 / 5 : ℂ) * s) / (s + 51 / 50) ^ 6) :=
      funext kernel_function_570
    rw [he]
    fun_prop (disch := exact pow_ne_zero 6 hden)
  exact
    hg.mul
      (hk.mul
        ((differentiable_id.const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt))

/-- At scale at least one, the reflected Gamma integral moves from the left
line to the central line. The horizontal limits, endpoint integrability and
holomorphy give a residue-free rectangle. -/
theorem reflected_gamma_shift_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) :
    (∫ t : ℝ, reflectedGammaIntegrand570 χ x (((-(9 / 16 : ℝ)) : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, reflectedGammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I) := by
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hi0 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand570 χ x (((-(9 / 16 : ℝ)) : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand570, mul_comm Complex.I, Complex.ofReal_neg] using
      (reflected_gamma_line_integrable_570 χ (c := -(9 / 16)) hx0 (by norm_num only)
        (by norm_num only) (by norm_num only))
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand570, mul_comm Complex.I, Complex.ofReal_zero] using
      (reflected_gamma_line_integrable_570 χ (c := 0) hx0 (by norm_num only) (by norm_num only)
        (by norm_num only))
  have htop := reflected_gamma_horizontal_570 χ hx 1 (Or.inl rfl)
  have hbot := reflected_gamma_horizontal_570 χ hx (-1) (Or.inr rfl)
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K :=
      reflectedGammaIntegrand570 χ x) (a := -(9 / 16 : ℝ)) (b := 0) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [T, reflectedGammaIntegrand570, neg_one_mul, Complex.ofReal_neg, neg_mul,
          sub_eq_add_neg, mul_assoc, one_mul] using hbot)
      (by simpa only [T, reflectedGammaIntegrand570, one_mul, mul_assoc] using htop)
      (by simpa only [Complex.ofReal_neg] using hi0) hi1
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
        (reflectedGammaIntegrand570 χ x) (((-(9 / 16 : ℝ)) : ℂ) - T n * Complex.I)
        ((0 : ℂ) + T n * Complex.I) =
      0 := by
    apply AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_zero_of_holomorphic
    intro z hz
    have hr := hz.1
    change z.re ∈ Set.uIcc _ _ at hr
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re, Complex.neg_re] at hr
    have hl : -(9 / 16 : ℝ) ≤ z.re := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact h.1
      · exact (by norm_num only : -(9 / 16 : ℝ) ≤ 0).trans h.1
    have hu : z.re ≤ 0 := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact h.2
      · exact h.2.trans (by norm_num only : -(9 / 16 : ℝ) ≤ 0)
    exact (reflected_gamma_differentiable_570 χ hx0 hl hu).differentiableWithinAt
  have he :=
    tendsto_nhds_unique ht
      (tendsto_const_nhds.congr
        (fun n ↦ by simpa only [Complex.ofReal_neg, Complex.ofReal_zero] using (hz n).symm))
  simpa only [Complex.ofReal_neg, Complex.ofReal_zero] using
    (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)).symm

/-- For a nonprincipal character and scale at least one, the actual reflected
archimedean contour equals the reflected central Gamma integral. -/
theorem reflected_arch_eq_central_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    reflectedArch570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, reflectedGammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)) := by
  rw [reflected_arch_eq_gamma_570 χ hne x]
  have h := reflected_gamma_shift_570 χ hx
  rw [← h]
  apply congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  have hr : (((-9 / 16 : ℝ) : ℂ)) = -(((9 / 16 : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hr]
  simp only [reflectedGammaIntegrand570, mul_comm Complex.I]
  congr 2
  push_cast
  ring

/-- The normalized central Gamma integral containing both reflected and
right logarithmic derivatives for an even character. -/
noncomputable def centralGammaPair570 {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.gammaFactor (1 / 2 - Complex.I * t) +
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)) *
        (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))

/-- For an even character, the two actual central Gamma integrals combine into
one integral with the two Gamma logarithmic derivatives. Absolute integrability
justifies adding the integrals. -/
theorem central_gamma_pair_eq_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, reflectedGammaIntegrand570 χ⁻¹ x ((0 : ℂ) + t * Complex.I))) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I))) =
      centralGammaPair570 χ x := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ reflectedGammaIntegrand570 χ⁻¹ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [reflectedGammaIntegrand570, mul_comm Complex.I, Complex.ofReal_zero] using
      (reflected_gamma_line_integrable_570 χ⁻¹ (c := 0) hx (by norm_num only) (by norm_num only)
        (by norm_num only))
  have hi2 :
    MeasureTheory.Integrable (fun t : ℝ ↦ gammaIntegrand570 χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [gammaIntegrand570, mul_comm Complex.I, Complex.ofReal_zero] using
      (gamma_line_integrable_570 χ (c := 0) hx (by norm_num only) (by norm_num only))
  unfold centralGammaPair570
  rw [← mul_add, ← MeasureTheory.integral_add hi1 hi2]
  apply congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  simp only [reflectedGammaIntegrand570, gammaIntegrand570, zero_add, mul_comm Complex.I, hγ]
  ring

/-- For an even character, the paired central Gamma contribution is the
integral of twice the real logarithmic derivative against the complex kernel. -/
theorem central_gamma_pair_real_570 {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even) (x : ℝ) :
    centralGammaPair570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (((2 : ℝ) * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re : ℝ) : ℂ) *
            (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  unfold centralGammaPair570
  apply congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  dsimp only
  have hs : star (Complex.I * (t : ℂ) + 1 / 2) = 1 / 2 - Complex.I * t := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
      map_one, map_ofNat]
    ring
  rw [← hs, refined_even_gamma_logDeriv_conj χ he]
  congr 1
  apply Complex.ext
  · simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re]
    ring
  · simp only [Complex.add_im, Complex.star_def, Complex.conj_im, Complex.ofReal_im]
    ring

/-- The even central Gamma pair is exactly the digamma integral appearing in
the refined paper formula, with the kernel's normalization retained. -/
theorem central_gamma_pair_digamma_570 {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even) (x : ℝ) :
    centralGammaPair570 χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi :
                ℝ) :
              ℂ) *
            (quarterKernel570.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  rw [central_gamma_pair_real_570 χ he x]
  apply congrArg (fun z : ℂ ↦ ((1 / (2 * Real.pi) : ℝ) : ℂ) * z)
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  dsimp only
  rw [refined_even_gamma_real_digamma χ he t]

/-- Under the section 31 counterexample hypotheses the central even Gamma pair
inherits the positive lower bound for the original contour cost. -/
theorem central_gamma_positive_570 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hS : 2 ≤ s)
    (pa : a.IsPrimitive) (pb : b.IsPrimitive) (pc : c.IsPrimitive) (na : a ≠ 1) (nb : b ≠ 1)
    (nc : c ≠ 1) (ia : a⁻¹ ≠ 1) (ib : b⁻¹ ≠ 1) (ic : c⁻¹ ≠ 1) {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1)
    (hlog : Real.log p + Real.log q + Real.log s ≤ 4 * r) (ea : a.Even) (eb : b.Even)
    (ec : c.Even) : 2 / 1000 < (centralGammaPair570 a (r ^ 2)).re := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ (show 1 ≤ r by linarith only [hl])
  have hh :=
    even_gamma_positive_570 hG a b c hP hQ hS pa pb pc na nb nc ia ib ic hl hu ht hA hB hC hlog ea
      eb ec
  rw [reflected_arch_eq_central_570 _ ia hx, right_gamma_eq_central_570 _ (zero_lt_one.trans_le hx),
    central_gamma_pair_eq_570 a ea (zero_lt_one.trans_le hx)] at hh
  exact hh

end PseudoPrime.PrimeTestBounds.MillerRabin
