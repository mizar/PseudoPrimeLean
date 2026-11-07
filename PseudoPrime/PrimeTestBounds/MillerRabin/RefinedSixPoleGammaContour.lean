/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualSigns
public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.NonnegativeStripLimits
public import PseudoPrime.LLS.PaperStatements.MellinKernelGammaPositiveScale

/-! # Gamma contour for the refined sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Gamma-factor logarithmic derivative times the sixth-pole kernel and
positive scale power is differentiable throughout the closed nonnegative strip.
The Gamma argument has positive real part and the kernel pole lies to the left. -/
theorem refined_gamma_integrand_differentiable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : 0 ≤ z.re) :
    DifferentiableAt ℂ
      (fun s : ℂ ↦
        logDeriv χ.gammaFactor (s + 1 / 2) * (refinedSixPoleKernel.function s * (x : ℂ) ^ s))
      z := by
  have hh : (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) := by
    push_cast; ring
  have hpos : 0 < (z + 1 / 2).re := by
    rw [hh, Complex.add_re, Complex.ofReal_re]
    linarith only [hz]
  have ha := AnalyticNumberTheory.DirichletLFunction.analyticAt_gammaFactor_of_re_pos χ hpos
  have hn := AnalyticNumberTheory.DirichletLFunction.gammaFactor_ne_zero_of_re_pos χ hpos
  have hg : DifferentiableAt ℂ (fun s : ℂ ↦ logDeriv χ.gammaFactor (s + 1 / 2)) z :=
    (ha.deriv.div ha hn).differentiableAt.comp z (differentiableAt_id.add_const _)
  have hden : z + (27 / 25 : ℂ) ≠ 0 := by
    intro h
    have h27 : (27 / 25 : ℂ) = (((27 / 25 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h27] at h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith only [hz, h']
  have hk : DifferentiableAt ℂ refinedSixPoleKernel.function z := by
    have he :
      refinedSixPoleKernel.function = fun s : ℂ ↦
        ((27 / 25 : ℂ) ^ 5) * (Complex.exp ((21 / 8 : ℂ) * s) / (s + 27 / 25) ^ 6) :=
      funext refined_six_pole_function
    rw [he]
    fun_prop (disch := exact pow_ne_zero 6 hden)
  exact
    hg.mul
      (hk.mul
        ((differentiable_id.const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).differentiableAt))

/-- On every vertical line between the center and `9/16`, the Gamma-factor
integrand is absolutely integrable. The admissible Mellin-kernel estimate
controls the logarithmic Gamma growth. -/
theorem refined_gamma_line_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x c : ℝ}
    (hx : 0 < x) (hc : 0 ≤ c) (hc' : c ≤ 9 / 16) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (((c : ℂ) + Complex.I * t) + 1 / 2) *
          (refinedSixPoleKernel.function ((c : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hi :=
    LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line refinedSixPoleKernel χ (c :=
      c) (x := x) (by linarith only [hc])
      (by
        rw [hd]; linarith only [hc'])
      (by linarith only [hc']) hx
  simpa only [mul_assoc] using hi

/-- The Gamma-factor logarithmic derivative weighted by the refined kernel
and the positive scale power. Its vertical integrals form the Gamma contour cost. -/
noncomputable def refinedGammaIntegrand {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  logDeriv χ.gammaFactor (s + 1 / 2) * (refinedSixPoleKernel.function s * (x : ℂ) ^ s)

/-- The `9/16` Gamma line equals the central line when both horizontal edges
vanish along integer heights. Analyticity and vertical integrability follow from
the refined kernel; only the horizontal decay remains to be supplied. -/
theorem refined_gamma_shift_of_horizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x)
    (hbottom :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ u in (0 : ℝ)..(9 / 16 : ℝ), refinedGammaIntegrand χ x ((u : ℂ) - (n : ℝ) * Complex.I))
        Filter.atTop (nhds 0))
    (htop :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ u in (0 : ℝ)..(9 / 16 : ℝ), refinedGammaIntegrand χ x ((u : ℂ) + (n : ℝ) * Complex.I))
        Filter.atTop (nhds 0)) :
    (∫ t : ℝ, refinedGammaIntegrand χ x (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I) := by
  have hi0 :
    MeasureTheory.Integrable (fun t : ℝ ↦ refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [refinedGammaIntegrand, mul_comm Complex.I, Complex.ofReal_zero] using
      (refined_gamma_line_integrable χ (c := 0) hx (by norm_num only) (by norm_num only))
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ refinedGammaIntegrand χ x (((9 / 16 : ℝ) : ℂ) + t * Complex.I)) := by
    simpa only [refinedGammaIntegrand, mul_comm Complex.I] using
      (refined_gamma_line_integrable χ (c := 9 / 16) hx (by norm_num only) (by norm_num only))
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K := refinedGammaIntegrand χ x)
      (a := 0) (b := 9 / 16) (fun n : ℕ ↦ (n : ℝ)) tendsto_natCast_atTop_atTop hbottom htop hi0 hi1
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral (refinedGammaIntegrand χ x)
        ((0 : ℂ) - n * Complex.I) (((9 / 16 : ℝ) : ℂ) + n * Complex.I) =
      0 := by
    apply AnalyticNumberTheory.RectangleGeometry.boundaryIntegral_zero_of_holomorphic
    intro s hs
    have hr := hs.1
    change s.re ∈ Set.uIcc _ _ at hr
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.natCast_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hr
    have hsr : 0 ≤ s.re := by
      rcases Set.mem_uIcc.mp hr with h | h
      · exact h.1
      · exact (by norm_num only : (0 : ℝ) ≤ 9 / 16).trans h.1
    exact (refined_gamma_integrand_differentiable χ hx hsr).differentiableWithinAt
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n ↦ (hz n).symm))
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)

/-- Under the horizontal-edge limits, the actual right Gamma contour equals
its central-line integral. This applies the vertical shift to the Gamma term in
the three-character cutoff inequality. -/
theorem refined_right_gamma_eq_central_of_horizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x)
    (hbottom :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ u in (0 : ℝ)..(9 / 16 : ℝ), refinedGammaIntegrand χ x ((u : ℂ) - (n : ℝ) * Complex.I))
        Filter.atTop (nhds 0))
    (htop :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ u in (0 : ℝ)..(9 / 16 : ℝ), refinedGammaIntegrand χ x ((u : ℂ) + (n : ℝ) * Complex.I))
        Filter.atTop (nhds 0)) :
    refinedRightGamma χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
  have h := refined_gamma_shift_of_horizontal χ hx hbottom htop
  unfold refinedRightGamma
  rw [← h]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  simp only [refinedGammaIntegrand, mul_comm Complex.I]

/-- The actual right Gamma contour equals its central-line integral at every
positive scale. The general positive-scale Gamma contour theorem supplies the
horizontal decay and the line shift for the sixth-pole Mellin kernel. -/
theorem refined_right_gamma_eq_central {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    refinedRightGamma χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have h :=
    LLS.PaperStatements.MellinKernel.gammaIntegral_eq_central_of_pos refinedSixPoleKernel χ (b :=
      9 / 16) (by norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx
  unfold refinedRightGamma
  rw [h]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  simp only [refinedGammaIntegrand, zero_add, mul_comm Complex.I]

/-- The three-character cutoff inequality with its right Gamma contribution
shifted to the central line, retaining the actual reflected Gamma term. -/
theorem refined_cutoff_central_right {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          3 *
            (refinedReflectedArchimedean a⁻¹ X +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ, refinedGammaIntegrand a X ((0 : ℂ) + t * Complex.I)))).re +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_explicit_costs hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB
      heC hX ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_right_gamma_eq_central a hx] at h
  exact h

/-- On every vertical line from `-9/16` to zero, the reflected Gamma-factor
integrand is absolutely integrable. Gamma's logarithmic growth is absorbed by
the admissible Mellin-kernel decay. -/
theorem refined_reflected_gamma_line_integrable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x c : ℝ} (hx : 0 < x) (hc : -(9 / 16 : ℝ) ≤ c) (hc' : c ≤ 0) (hcne : c ≠ -1 / 2) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        logDeriv χ.gammaFactor (1 / 2 - ((c : ℂ) + Complex.I * t)) *
          (refinedSixPoleKernel.function ((c : ℂ) + Complex.I * t) *
            (x : ℂ) ^ ((c : ℂ) + Complex.I * t))) := by
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
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
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line refinedSixPoleKernel (c := c)
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
theorem refined_reflected_gamma_horizontal {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ σ in (-(9 / 16 : ℝ))..(0 : ℝ),
          logDeriv χ.gammaFactor (1 / 2 - ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) *
            refinedSixPoleKernel.function ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) *
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
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  apply
    LLS.PaperStatements.MellinKernel.tendsto_horizontalIntegral_of_scaled_bound refinedSixPoleKernel
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
noncomputable def refinedReflectedGammaIntegrand {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (s : ℂ) : ℂ :=
  logDeriv χ.gammaFactor (1 / 2 - s) * (refinedSixPoleKernel.function s * (x : ℂ) ^ s)

/-- The reflected Gamma integrand is differentiable between the left contour
and the central line. Both the Gamma argument and the distance from the kernel
pole have positive real part there. -/
theorem refined_reflected_gamma_differentiable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : -(9 / 16 : ℝ) ≤ z.re) (hz' : z.re ≤ 0) :
    DifferentiableAt ℂ (refinedReflectedGammaIntegrand χ x) z := by
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
  have hden : z + (27 / 25 : ℂ) ≠ 0 := by
    intro h
    have h27 : (27 / 25 : ℂ) = (((27 / 25 : ℝ)) : ℂ) := by
      push_cast; ring
    rw [h27] at h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
    linarith only [hz, h']
  have hk : DifferentiableAt ℂ refinedSixPoleKernel.function z := by
    have he :
      refinedSixPoleKernel.function = fun s : ℂ ↦
        ((27 / 25 : ℂ) ^ 5) * (Complex.exp ((21 / 8 : ℂ) * s) / (s + 27 / 25) ^ 6) :=
      funext refined_six_pole_function
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
theorem refined_reflected_gamma_shift {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) :
    (∫ t : ℝ, refinedReflectedGammaIntegrand χ x (((-(9 / 16 : ℝ)) : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, refinedReflectedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I) := by
  let T := fun n : ℕ ↦ (n : ℝ) + 1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hi0 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ refinedReflectedGammaIntegrand χ x (((-(9 / 16 : ℝ)) : ℂ) + t * Complex.I)) := by
    simpa only [refinedReflectedGammaIntegrand, mul_comm Complex.I, Complex.ofReal_neg] using
      (refined_reflected_gamma_line_integrable χ (c := -(9 / 16)) hx0 (by norm_num only)
        (by norm_num only) (by norm_num only))
  have hi1 :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ refinedReflectedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
    simpa only [refinedReflectedGammaIntegrand, mul_comm Complex.I, Complex.ofReal_zero] using
      (refined_reflected_gamma_line_integrable χ (c := 0) hx0 (by norm_num only) (by norm_num only)
        (by norm_num only))
  have htop := refined_reflected_gamma_horizontal χ hx 1 (Or.inl rfl)
  have hbot := refined_reflected_gamma_horizontal χ hx (-1) (Or.inr rfl)
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_boundaryIntegral (K :=
      refinedReflectedGammaIntegrand χ x) (a := -(9 / 16 : ℝ)) (b := 0) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [T, refinedReflectedGammaIntegrand, neg_one_mul, Complex.ofReal_neg, neg_mul,
          sub_eq_add_neg, mul_assoc, one_mul] using hbot)
      (by simpa only [T, refinedReflectedGammaIntegrand, one_mul, mul_assoc] using htop)
      (by simpa only [Complex.ofReal_neg] using hi0) hi1
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral
        (refinedReflectedGammaIntegrand χ x) (((-(9 / 16 : ℝ)) : ℂ) - T n * Complex.I)
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
    exact (refined_reflected_gamma_differentiable χ hx0 hl hu).differentiableWithinAt
  have he :=
    tendsto_nhds_unique ht
      (tendsto_const_nhds.congr
        (fun n ↦ by simpa only [Complex.ofReal_neg, Complex.ofReal_zero] using (hz n).symm))
  simpa only [Complex.ofReal_neg, Complex.ofReal_zero] using
    (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)).symm

/-- For a nonprincipal character and scale at least one, the actual reflected
archimedean contour equals the reflected central Gamma integral. -/
theorem refined_reflected_arch_eq_central {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedArchimedean χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, refinedReflectedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)) := by
  rw [refined_reflected_arch_eq_gamma χ hne x]
  have h := refined_reflected_gamma_shift χ hx
  rw [← h]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  have hr : (((-9 / 16 : ℝ) : ℂ)) = -(((9 / 16 : ℝ) : ℂ)) := by
    push_cast; ring
  rw [hr]
  simp only [refinedReflectedGammaIntegrand, mul_comm Complex.I]
  congr 2
  push_cast
  ring

/-- The three-character cutoff inequality with both actual Gamma contours
moved to the central line and with explicit conductor and reflected Euler costs. -/
theorem refined_cutoff_central_both {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          3 *
            ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ, refinedReflectedGammaIntegrand a⁻¹ X ((0 : ℂ) + t * Complex.I))) +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ, refinedGammaIntegrand a X ((0 : ℂ) + t * Complex.I)))).re +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_central_right hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hx1 : (1 : ℝ) ≤ X := (by norm_num only : (1 : ℝ) ≤ 1000).trans hX
  rw [refined_reflected_arch_eq_central a⁻¹ hiA hx1] at h
  exact h

/-- The normalized central Gamma integral containing both reflected and
right logarithmic derivatives for an even character. -/
noncomputable def refinedCentralGammaPair {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      (logDeriv χ.gammaFactor (1 / 2 - Complex.I * t) +
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)) *
        (refinedSixPoleKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))

/-- For an even character, the two actual central Gamma integrals combine into
one integral with the two Gamma logarithmic derivatives. Absolute integrability
justifies adding the integrals. -/
theorem refined_central_gamma_pair_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    {x : ℝ} (hx : 0 < x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, refinedReflectedGammaIntegrand χ⁻¹ x ((0 : ℂ) + t * Complex.I))) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ, refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I))) =
      refinedCentralGammaPair χ x := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
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
  unfold refinedCentralGammaPair
  rw [← mul_add, ← MeasureTheory.integral_add hi1 hi2]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  simp only [refinedReflectedGammaIntegrand, refinedGammaIntegrand, zero_add, mul_comm Complex.I,
    hγ]
  ring

/-- The refined cutoff bound with both central Gamma terms combined into
one integral, while retaining the explicit conductor and Euler costs. -/
theorem refined_cutoff_central_pair {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) {X : ℝ} (hX : 1000 ≤ X) (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    4 *
          (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X n).re <
      (Real.log p + Real.log q + Real.log r) *
            (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) *
              X ^ (-(27 / 25 : ℝ)) *
              ((21 / 8 : ℝ) + Real.log X) ^ 5) +
          3 * (refinedCentralGammaPair a X).re +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_central_both hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  rw [refined_central_gamma_pair_eq a heA hx] at h
  exact h

/-- The logarithmic derivative of an even character's Gamma factor commutes
with complex conjugation, including at points where the totalized quotient vanishes. -/
theorem refined_even_gamma_logDeriv_conj {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (s : ℂ) : logDeriv χ.gammaFactor (star s) = star (logDeriv χ.gammaFactor s) := by
  have hg : χ.gammaFactor = Complex.Gammaℝ := by
    funext z
    exact he.gammaFactor_def z
  rw [hg]
  have heq : (star ∘ Complex.Gammaℝ ∘ star) = Complex.Gammaℝ := by
    funext z
    simp only [Function.comp_def, Complex.star_def, Complex.Gammaℝ_conj, Complex.conj_conj]
  have hd := congrFun (deriv_star_conj (f := Complex.Gammaℝ)) (star s)
  simp only [Complex.star_def, Function.comp_def, Complex.conj_conj] at heq hd
  rw [heq] at hd
  simp only [logDeriv_apply, Complex.star_def, map_div₀]
  rw [hd, Complex.Gammaℝ_conj]

/-- For an even character, the paired central Gamma contribution is the
integral of twice the real logarithmic derivative against the complex kernel. -/
theorem refined_central_gamma_pair_real {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even) (x : ℝ) :
    refinedCentralGammaPair χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (((2 : ℝ) * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re : ℝ) : ℂ) *
            (refinedSixPoleKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  unfold refinedCentralGammaPair
  congr 1
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

/-- The paired real Gamma logarithmic derivative on the critical line is the
real digamma value at `1/4 + it/2` minus `log π`. -/
theorem refined_even_gamma_real_digamma {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even) (t : ℝ) :
    2 * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re =
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi := by
  have hpos : 0 < (Complex.I * (t : ℂ) + 1 / 2).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re]
    norm_num only
  have hhalf : ∀ m : ℕ, (Complex.I * (t : ℂ) + 1 / 2) / 2 ≠ -(m : ℂ) := by
    simpa only [Complex.ofReal_zero, add_zero] using
      (AnalyticNumberTheory.DirichletLFunction.half_add_ne_neg_nat_of_re_pos hpos (a := 0) le_rfl)
  rw [AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma he hhalf]
  have harg :
    (Complex.I * (t : ℂ) + 1 / 2) / 2 = (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ)) := by
    push_cast; ring
  rw [harg, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
  ring

/-- The even central Gamma pair is exactly the digamma integral appearing in
the refined paper formula, with the kernel's normalization retained. -/
theorem refined_central_gamma_pair_digamma {q : ℕ} (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (x : ℝ) :
    refinedCentralGammaPair χ x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi :
                ℝ) :
              ℂ) *
            (refinedSixPoleKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  rw [refined_central_gamma_pair_real χ he x]
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply MeasureTheory.ae_of_all
  intro t
  dsimp only
  rw [refined_even_gamma_real_digamma χ he t]

end PseudoPrime.PrimeTestBounds.MillerRabin
