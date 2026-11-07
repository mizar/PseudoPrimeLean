/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleGammaContour
public import PseudoPrime.Analysis.TriangularDigammaCorrection
public import PseudoPrime.LLS.PaperStatements.TriangularEvenBaseline
public import PseudoPrime.AnalyticNumberTheory.Gamma.GammaFactorRefinedBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass
public import PseudoPrime.Analysis.CauchyPowerIntegrals

/-! # Explicit central digamma bound for the refined kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The vertical increment of the real digamma function at `1/4` is bounded
by `18 t^2` at height `t/2`. Bound its positive reciprocal series by four times
the shifted inverse-square series, whose sum is at most eighteen. -/
theorem refined_digamma_vertical_le (t : ℝ) :
    (Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re -
        (Complex.digamma (((1 / 4 : ℝ) : ℂ))).re ≤
      18 * t ^ 2 := by
  let a : ℝ := 1 / 4
  let u : ℝ := t / 2
  have ha : 0 < a := by norm_num only [a]
  have hc := AnalyticNumberTheory.Gamma.summable_vertical_digamma_correction (a := a) (t := u) ha
  have hs := Analysis.summable_shifted_inverse_squares ha
  have hp (n : ℕ) : u ^ 2 / ((a + n) * ((a + n) ^ 2 + u ^ 2)) ≤ (4 * u ^ 2) * ((a + n) ^ 2)⁻¹ := by
    have hq : 1 / 4 ≤ a + n := by
      dsimp only [a]
      linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hpos : 0 < a + n := lt_of_lt_of_le (by norm_num only) hq
    have hden : 0 < (a + n) * ((a + n) ^ 2 + u ^ 2) :=
      mul_pos hpos (add_pos_of_pos_of_nonneg (sq_pos_of_pos hpos) (sq_nonneg u))
    have hsq : 0 < (a + n) ^ 2 := sq_pos_of_pos hpos
    rw [← div_eq_mul_inv]
    apply (div_le_div_iff₀ hden hsq).mpr
    have hfour : 0 ≤ 4 * (a + n) - 1 := by
      norm_num only at hq ⊢
      linarith only [hq]
    have haux := mul_nonneg hfour (sq_nonneg (a + n))
    have haux2 := mul_nonneg hpos.le (sq_nonneg u)
    have hb : (a + n) ^ 2 ≤ 4 * ((a + n) * ((a + n) ^ 2 + u ^ 2)) := by nlinarith only [haux, haux2]
    have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg u)
    nlinarith only [hmul]
  have hm := hc.tsum_le_tsum hp (hs.mul_left (4 * u ^ 2))
  rw [tsum_mul_left] at hm
  have hsum := Analysis.shifted_inverse_square_sum_le_eighteen (b := a) (by norm_num only [a])
  have h :=
    mul_le_mul_of_nonneg_left hsum (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num only) (sq_nonneg u))
  change (Complex.digamma ((a : ℂ) + Complex.I * u)).re - (Complex.digamma (a : ℂ)).re ≤ 18 * t ^ 2
  rw [AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum ha]
  dsimp only [u] at hm h
  nlinarith only [hm, h, sq_nonneg t]

/-- The real-axis digamma baseline at one quarter differs from `log π` in
absolute value by at most six. Use the digamma recurrence and positivity at two. -/
theorem refined_digamma_baseline_abs :
    |(Complex.digamma (((1 / 4 : ℝ) : ℂ))).re - Real.log Real.pi| ≤ (6 : ℝ) := by
  have h2 : 0 < (Complex.digamma ((2 : ℝ) : ℂ)).re := by
    have hv := Complex.digamma_nat_add_one 1
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat, harmonic, Finset.sum_range_succ,
      Finset.sum_range_zero] at hv
    have hv' := congrArg Complex.re hv
    norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_ofNat, Complex.one_re] at hv'
    norm_num only [Complex.ofReal_ofNat]
    linarith only [hv', Real.eulerMascheroniConstant_lt_two_thirds]
  have hm :=
    AnalyticNumberTheory.Gamma.re_digamma_mono_of_pos (by norm_num only : (0 : ℝ) < 2)
      (by norm_num only : (2 : ℝ) ≤ 9 / 4)
  have hrec :=
    congrArg Complex.re
      (Complex.digamma_apply_add_nat (s := ((1 / 4 : ℝ) : ℂ))
        (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos (by norm_num only [Complex.ofReal_re])) 2)
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, Complex.add_re, Complex.ofReal_re] at hrec
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_ofNat] at hrec
  have hpi := AnalyticNumberTheory.Gamma.real_log_pi_le_six_fifths
  have hupper := LLS.PaperStatements.gamma_even_baseline_lt
  apply abs_le.mpr
  constructor <;> linarith only [h2, hm, hrec, hpi, hupper]

/-- The real digamma factor in the central Gamma integral is bounded by
`6 + 18 t^2`. The vertical correction is nonnegative and has the proved
quadratic upper bound. -/
theorem refined_digamma_central_abs (t : ℝ) :
    |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi| ≤
      6 + 18 * t ^ 2 := by
  have hl :=
    AnalyticNumberTheory.Gamma.digamma_vertical_re_ge_real (a := 1 / 4) (t := t / 2)
      (by norm_num only)
  have hu := refined_digamma_vertical_le t
  have hb := refined_digamma_baseline_abs
  apply abs_le.mpr
  have hb' := abs_le.mp hb
  constructor <;> linarith only [hl, hu, hb'.1, hb'.2, sq_nonneg t]

/-- The second moment of the normalized sixth-order Cauchy weight is `π/8`.
Subtract the exact third Cauchy integral from the second. -/
theorem refined_cauchy_second_moment : (∫ t : ℝ, t ^ 2 / (1 + t ^ 2) ^ 3) = Real.pi / 8 := by
  have he (t : ℝ) : t ^ 2 / (1 + t ^ 2) ^ 3 = 1 / (1 + t ^ 2) ^ 2 - 1 / (1 + t ^ 2) ^ 3 := by
    have hn : 1 + t ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg t])
    field_simp
    ring
  have h2 := Analysis.integrable_cauchy_power (by norm_num only : 1 ≤ 2)
  have h3 := Analysis.integrable_cauchy_power (by norm_num only : 1 ≤ 3)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_sub h2 h3, Analysis.integral_cauchy_power_two,
    Analysis.integral_cauchy_power_three]
  ring

/-- The second height moment of the actual normalized sixth-pole kernel is
`π(27/25)^2/8`. Scale the normalized Cauchy moment by the pole location. -/
theorem refined_six_pole_second_moment :
    (∫ t : ℝ, t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖) =
      Real.pi * (27 / 25 : ℝ) ^ 2 / 8 := by
  have he (t : ℝ) :
    t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖ =
      (27 / 25 : ℝ) * (((25 / 27 : ℝ) * t) ^ 2 / (1 + ((25 / 27 : ℝ) * t) ^ 2) ^ 3) := by
    rw [refined_six_pole_norm]
    have h1 : (27 / 25 : ℝ) ^ 2 + t ^ 2 ≠ 0 := by positivity
    have h2 : 1 + ((25 / 27 : ℝ) * t) ^ 2 ≠ 0 := by positivity
    field_simp
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he),
    MeasureTheory.integral_const_mul,
    MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ ↦ t ^ 2 / (1 + t ^ 2) ^ 3)
      (25 / 27 : ℝ),
    refined_cauchy_second_moment, smul_eq_mul]
  norm_num only
  ring

/-- The second height moment of the sixth-pole kernel is integrable. Scale
the difference of the integrable second and third Cauchy powers. -/
theorem refined_six_pole_second_integrable :
    MeasureTheory.Integrable
      (fun t : ℝ ↦ t ^ 2 * ‖refinedSixPoleKernel.function (Complex.I * t)‖) := by
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
              (by norm_num only : (25 / 27 : ℝ) ≠ 0)).mpr
          hn).const_mul
      (27 / 25 : ℝ)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [refined_six_pole_norm]
  have h1 : (27 / 25 : ℝ) ^ 2 + t ^ 2 ≠ 0 := by positivity
  have h2 : 1 + ((25 / 27 : ℝ) * t) ^ 2 ≠ 0 := by positivity
  field_simp

/-- For an even character, the sum of the reflected and right central
Gamma integrands equals the real digamma factor times the complex kernel phase. -/
theorem refined_even_gamma_integrand_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) (x t : ℝ) :
    refinedReflectedGammaIntegrand χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
        refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I) =
      (((Complex.digamma (((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2 : ℝ))).re - Real.log Real.pi : ℝ) :
          ℂ) *
        (refinedSixPoleKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)) := by
  have heinv : χ⁻¹.Even := AnalyticNumberTheory.DirichletLFunction.character_even_inv_iff.mpr he
  have hγ : χ⁻¹.gammaFactor = χ.gammaFactor := by
    funext z
    rw [heinv.gammaFactor_def, he.gammaFactor_def]
  have hs : star (Complex.I * (t : ℂ) + 1 / 2) = 1 / 2 - Complex.I * t := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
      map_one, map_ofNat]
    ring
  have hd := refined_even_gamma_real_digamma χ he t
  unfold refinedReflectedGammaIntegrand refinedGammaIntegrand
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

/-- The paired even central Gamma integral is bounded by its exact normalized
mass and second moment. The bound uses the `6 + 18 t^2` digamma envelope. -/
theorem refined_central_gamma_pair_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    ‖refinedCentralGammaPair χ x‖ ≤ (9 / 8 : ℝ) + (9 / 8 : ℝ) * (27 / 25 : ℝ) ^ 2 := by
  let F := fun t : ℝ ↦
    refinedReflectedGammaIntegrand χ⁻¹ x ((0 : ℂ) + t * Complex.I) +
      refinedGammaIntegrand χ x ((0 : ℂ) + t * Complex.I)
  let K := fun t : ℝ ↦ ‖refinedSixPoleKernel.function (Complex.I * t)‖
  let B := fun t : ℝ ↦ 6 * K t + 18 * (t ^ 2 * K t)
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
  have hfi : MeasureTheory.Integrable F := hi1.add hi2
  have hk : MeasureTheory.Integrable K := by
    have h :=
      (LLS.PaperStatements.MellinKernel.integrable_line refinedSixPoleKernel (c := 0)
          (by norm_num only) (by linarith only [refinedSixPoleKernel.delta_pos])).norm
    simpa only [K, Complex.ofReal_zero, zero_add] using h
  have hB : MeasureTheory.Integrable B :=
    (hk.const_mul 6).add (refined_six_pole_second_integrable.const_mul 18)
  have hpoint (t : ℝ) : ‖F t‖ ≤ B t := by
    dsimp only [F, B, K]
    rw [refined_even_gamma_integrand_eq χ he x t, norm_mul, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have h :=
      mul_le_mul_of_nonneg_right (refined_digamma_central_abs t)
        (norm_nonneg (refinedSixPoleKernel.function (Complex.I * t)))
    nlinarith only [h]
  have hbound :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hB hpoint)
  have hmass : (∫ t : ℝ, K t) = 3 * Real.pi / 8 := by
    have h := refined_six_pole_mass
    change (∫ t : ℝ, K t) / (2 * Real.pi) = 3 / 16 at h
    have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
    field_simp at h
    linarith only [h]
  change ‖refinedCentralGammaPair χ x‖ ≤ _
  rw [← refined_central_gamma_pair_eq χ he hx, ← mul_add, ← MeasureTheory.integral_add hi1 hi2]
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))]
  apply
    (mul_le_mul_of_nonneg_left hbound
        (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))).trans_eq
  have he : (∫ t : ℝ, B t) = 6 * (3 * Real.pi / 8) + 18 * (Real.pi * (27 / 25 : ℝ) ^ 2 / 8) := by
    dsimp only [B]
    rw [MeasureTheory.integral_add (hk.const_mul 6)
        (refined_six_pole_second_integrable.const_mul 18),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hmass,
      refined_six_pole_second_moment]
  rw [he]
  field_simp [Real.pi_pos.ne']
  ring

/-- For three even characters, the common central Gamma cost is strictly
below five times the kernel normalization. This is the paper's Gamma budget. -/
theorem refined_three_gamma_lt {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even) {x : ℝ}
    (hx : 0 < x) : 3 * (refinedCentralGammaPair χ x).re < 5 * (27 / 25 : ℝ) ^ 5 := by
  have hr := Complex.re_le_norm (refinedCentralGammaPair χ x)
  have hb := refined_central_gamma_pair_bound χ he hx
  have hn : (3 : ℝ) * (9 / 8 + (9 / 8) * (27 / 25) ^ 2) < 5 * (27 / 25) ^ 5 := by norm_num only
  linarith only [hr, hb, hn]

/-- Under the three prime-prefix conditions, the refined cutoff deficit has
explicit conductor, reflected Euler, zero-mass and Gamma costs. The Gamma
cost is strictly less than five times the kernel normalization. -/
theorem refined_cutoff_gamma_bounded {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
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
          5 * (27 / 25 : ℝ) ^ 5 +
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
            X ^ (-(27 / 25 : ℝ)) *
            (((21 / 8 : ℝ) + Real.log X) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
              (25 / 2 : ℝ) ^ 5 * ((50 / 9 : ℝ) ^ 2 + 50 / 59)) +
          (3 / 16 : ℝ) * (Real.log p + Real.log q + Real.log r) -
        (6366 / 1000 : ℝ) * (27 / 25 : ℝ) ^ 5 := by
  have h :=
    refined_cutoff_central_pair hGRH a b c hP hQ hR hpA hpB hpC hnA hnB hnC hiA hiB hiC heA heB heC
      hX ht hA hB hC
  have hx : 0 < X := by linarith only [hX]
  have hg := refined_three_gamma_lt a heA hx
  linarith only [h, hg]

end PseudoPrime.PrimeTestBounds.MillerRabin
