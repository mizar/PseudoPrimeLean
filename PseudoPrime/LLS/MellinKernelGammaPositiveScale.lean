/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelGammaBounds

/-!
# Gamma contour shifts at every positive scale

Extend the horizontal limit and right-to-central Gamma integral equality to scales
below one, so the exact dual-scale formula can use central-line evaluations.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

/-- For a positive scale at most one and a nonnegative strip interval, the complex
power has norm at most one. Absorb it into the input function and apply the existing
horizontal decay theorem at unit scale. This supplies the small-scale contour limit. -/
theorem tendsto_nonnegative_horizontalIntegral_of_le_one (K : MellinKernel) {b x : ℝ} (hb : 0 ≤ b)
    (hbK : b ≤ 1 / 2 + K.delta) (hx : 0 < x) (hx1 : x ≤ 1) (T ε : ℕ → ℝ) (ht : ∀ n, 1 ≤ |T n|)
    (hε : ∀ n, 0 ≤ ε n) (hlim : Filter.Tendsto ε Filter.atTop (nhds 0)) (F : ℂ → ℂ)
    (hF : ∀ n, ∀ σ ∈ Set.uIoc 0 b, ‖F ((σ : ℂ) + T n * Complex.I)‖ ≤ ε n * (T n) ^ 2) :
    Filter.Tendsto
      (fun n : ℕ ↦
        ∫ σ in 0..b,
          F ((σ : ℂ) + T n * Complex.I) * K.function ((σ : ℂ) + T n * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + T n * Complex.I))
      Filter.atTop (nhds 0) := by
  have hbound (n : ℕ) (σ : ℝ) (hσ : σ ∈ Set.uIoc 0 b) :
    ‖F ((σ : ℂ) + T n * Complex.I) * (x : ℂ) ^ ((σ : ℂ) + T n * Complex.I)‖ ≤ ε n * (T n) ^ 2 := by
    have hσ' : 0 < σ ∧ σ ≤ b := by simpa only [Set.uIoc_of_le hb, Set.mem_Ioc] using hσ
    have hp : ‖(x : ℂ) ^ ((σ : ℂ) + T n * Complex.I)‖ ≤ 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      exact Real.rpow_le_one hx.le hx1 hσ'.1.le
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans (by simpa only [mul_one] using hF n σ hσ)
  have h :=
    tendsto_horizontalIntegral_of_scaled_bound K hb (by linarith only [K.delta_pos]) hbK (x := 1)
      le_rfl T ε ht hε hlim (fun s ↦ F s * (x : ℂ) ^ s) hbound
  simpa only [Complex.ofReal_one, Complex.one_cpow, mul_one, one_mul, mul_assoc, mul_comm,
    mul_left_comm] using h

open AnalyticNumberTheory.DirichletLFunction in
/-- For a positive scale at most one, a nonnegative admissible strip and either signed
height sequence, the Gamma horizontal integral tends to zero. The logarithmic Gamma
bound and the unit-scale decay majorant remove the horizontal contour edges. -/
theorem tendsto_gamma_horizontalIntegral_of_le_one (K : MellinKernel) {N : ℕ}
    (χ : DirichletCharacter ℂ N) {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + K.delta)
    (hb2 : b ≤ 3 / 2) (hx : 0 < x) (hx1 : x ≤ 1) (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ σ in 0..b,
          logDeriv χ.gammaFactor (((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) + 1 / 2) *
            K.function ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  let T := fun n : ℕ => (n : ℝ) + 1
  let G : ℝ :=
    ‖Complex.log (Real.pi : ℂ)‖ + Real.pi + AnalyticNumberTheory.Gamma.digammaLogErrorBound + 4
  let D := |G| + Real.log 5 + 1
  have ht (n : ℕ) : 1 ≤ T n := le_add_of_nonneg_left (Nat.cast_nonneg n)
  have heabs (n : ℕ) : |e * T n| = T n := by
    rcases he with rfl | rfl
    · rw [one_mul, abs_of_nonneg (zero_le_one.trans (ht n))]
    · rw [neg_one_mul, abs_neg, abs_of_nonneg (zero_le_one.trans (ht n))]
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact add_nonneg (add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num only))) zero_le_one
  have hT : Filter.Tendsto T Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  apply
    tendsto_nonnegative_horizontalIntegral_of_le_one K hb hbK hx hx1 (fun n => e * T n)
      (fun n => (Real.log (T n) + D) / (T n) ^ 2)
      (fun n => by
        rw [heabs]; exact ht n)
      (fun n => div_nonneg (add_nonneg (Real.log_nonneg (ht n)) hD) (sq_nonneg _))
      (AnalyticNumberTheory.General.tendsto_log_add_const_div_sq_atTop D |>.comp hT)
      (fun s : ℂ => logDeriv χ.gammaFactor (s + 1 / 2))
  intro n σ hσ
  have hσ' : 0 < σ ∧ σ ≤ b := by simpa only [Set.uIoc_of_le hb, Set.mem_Ioc] using hσ
  have hsr : |(((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) + 1 / 2).re| ≤ 2 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.div_ofNat_re, Complex.one_re]
    exact abs_le.mpr ⟨by linarith only [hσ'.1], by linarith only [hσ'.2, hb2]⟩
  have hsi : (((σ : ℂ) + ((e * T n : ℝ) : ℂ) * Complex.I) + 1 / 2).im = e * T n := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, add_zero, zero_add, Complex.div_ofNat_im, Complex.one_im,
      zero_div]
  have hg :=
    norm_logDeriv_gammaFactor_le_log χ hsr
      (by
        rw [hsi, heabs]; exact ht n)
  rw [hsi, heabs] at hg
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

open AnalyticNumberTheory.DirichletLFunction in
/-- For every positive scale, the Gamma horizontal integrals vanish on a nonnegative
admissible strip. Split at scale one and combine the two established decay estimates.
This is the horizontal limit required for inverse-scale Gamma line shifts. -/
theorem tendsto_gamma_horizontalIntegral_of_pos (K : MellinKernel) {N : ℕ}
    (χ : DirichletCharacter ℂ N) {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + K.delta)
    (hb2 : b ≤ 3 / 2) (hx : 0 < x) (e : ℝ) (he : e = 1 ∨ e = -1) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ σ in 0..b,
          logDeriv χ.gammaFactor (((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) + 1 / 2) *
            K.function ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I) *
            (x : ℂ) ^ ((σ : ℂ) + ((e * ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  by_cases hx1 : 1 ≤ x
  · exact tendsto_gamma_horizontalIntegral K χ hb hbK hb2 hx1 e he
  · exact tendsto_gamma_horizontalIntegral_of_le_one K χ hb hbK hb2 hx (lt_of_not_ge hx1).le e he

open AnalyticNumberTheory.DirichletLFunction in
/-- For every positive scale and nonnegative admissible line below three halves, the
Gamma integral equals its central-line integral. Absolute vertical integrability,
holomorphy on the strip and vanishing horizontal edges justify Cauchy line shifting.
This allows the central Gamma evaluations to be used at inverse scales. -/
theorem gammaIntegral_eq_central_of_pos (K : MellinKernel) {N : ℕ} (χ : DirichletCharacter ℂ N)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + K.delta) (hb2 : b ≤ 3 / 2) (hx : 0 < x) :
    (∫ t : ℝ,
        logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  let F := fun s : ℂ => logDeriv χ.gammaFactor (s + 1 / 2) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ => (n : ℝ) + 1
  have hxpos : 0 < x := hx
  have hb' : -1 / 2 < b := by linarith only [hb]
  have h0 : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  have hi0 :=
    integrable_gammaFactor_power_line K χ (c := 0) (by norm_num only) h0 (by norm_num only) hxpos
  have hib := integrable_gammaFactor_power_line K χ hb' hbK hb2 hxpos
  have htop := tendsto_gamma_horizontalIntegral_of_pos K χ hb hbK hb2 hx 1 (Or.inl rfl)
  have hbot := tendsto_gamma_horizontalIntegral_of_pos K χ hb hbK hb2 hx (-1) (Or.inr rfl)
  have ht :=
    AnalyticNumberTheory.RectangleGeometry.tendsto_rectangleBoundaryIntegral_of_horizontal_limits
      (K := F) (a := 0) (b := b) T
      (Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (by
        simpa only [F, T, neg_one_mul, Complex.ofReal_neg, neg_mul, sub_eq_add_neg, one_mul] using
          hbot)
      (by simpa only [F, T, one_mul] using htop) (by simpa only [F, mul_comm] using hi0)
      (by simpa only [F, mul_comm] using hib)
  have hz (n : ℕ) :
    AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral F ((0 : ℂ) - T n * Complex.I)
        ((b : ℂ) + T n * Complex.I) =
      0 := by
    apply
      AnalyticNumberTheory.RectangleGeometry.rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    intro s hs
    have hsr : 0 ≤ s.re ∧ s.re ≤ b := by
      have hs' := hs.1
      change s.re ∈ Set.uIcc _ _ at hs'
      simpa only [Complex.sub_re, Complex.add_re, Complex.zero_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
        add_zero, Set.uIcc_of_le hb, Set.mem_Icc] using hs'
    have hreg : s ∈ K.region :=
      K.strip_subset ⟨by linarith only [hsr.1, K.delta_pos], hsr.2.trans hbK⟩
    have hsp : s ≠ -1 / 2 := by
      intro he
      have hre := congrArg Complex.re he
      norm_num only [Complex.neg_re, Complex.div_ofNat_re, Complex.one_re] at hre
      linarith only [hsr.1, hre]
    have hk :=
      K.holomorphic.differentiableAt ((K.region_open.sdiff isClosed_singleton).mem_nhds ⟨hreg, hsp⟩)
    have hsg : 0 < (s + 1 / 2).re := by
      simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re]
      linarith only [hsr.1]
    have hg := analyticAt_gammaFactor_of_re_pos χ hsg
    have hl := (hg.deriv.div hg (gammaFactor_ne_zero_of_re_pos χ hsg)).differentiableAt
    have hf :=
      (hl.comp s (differentiableAt_id.add_const (1 / 2))).mul hk |>.mul
        ((differentiable_id.const_cpow
            (Or.inl (Complex.ofReal_ne_zero.mpr hxpos.ne'))).differentiableAt)
    exact hf.differentiableWithinAt
  have he := tendsto_nhds_unique ht (tendsto_const_nhds.congr (fun n => (hz n).symm))
  have hi := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left Complex.I_ne_zero)
  simpa only [F, Complex.ofReal_zero, zero_add, mul_comm, mul_assoc, mul_left_comm] using hi

end PseudoPrime.LLS.PaperStatements.MellinKernel
