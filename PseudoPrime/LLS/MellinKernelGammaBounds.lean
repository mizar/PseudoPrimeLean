/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelVerticalIntegrability
public import PseudoPrime.LLS.MellinKernelZeros
public import PseudoPrime.LLS.MellinKernelHorizontal
public import PseudoPrime.AnalyticNumberTheory.General.LogPolynomialDecay

/-!
# Uniform archimedean bounds for Mellin kernels

The gamma integral on the imaginary Mellin line is bounded independently of the character,
modulus and positive scale. Kernel decay makes the logarithmic growth majorant integrable.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements.MellinKernel

open AnalyticNumberTheory.DirichletLFunction in
/-- For any Mellin kernel there is a positive constant bounding the normalized central-line
gamma integral for every character, modulus and positive scale. The two parity factors
have a common logarithmic bound; kernel decay supplies an integrable inverse-square
majorant. The phase has norm one. This gives the central-line archimedean error bound
needed after shifting the right gamma contour. -/
theorem exists_norm_central_gammaIntegral_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) {x : ℝ},
          0 < x →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                      (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))‖ ≤
              C := by
  obtain ⟨A, hA, hbA⟩ :=
    exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log (σ := 1 / 2) (by norm_num only)
      (by norm_num only)
  obtain ⟨B, hB, hbB⟩ := exists_vertical_decay_bound K
  let H := fun t : ℝ => (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  let D := (A * B) * (∫ t : ℝ, H t)
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  refine ⟨1 + ‖d‖ * max D 0, ?_, fun N χ x hx => ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg (norm_nonneg _) (le_max_right _ _))
  · let F := fun t : ℝ =>
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))
    have hiF : MeasureTheory.Integrable F := by
      have hc' : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
      have hi :=
        integrable_gammaFactor_power_line K χ (c := 0) (by norm_num only) hc' (by norm_num only) hx
      simpa only [F, Complex.ofReal_zero, zero_add, mul_assoc] using hi
    have hb (t : ℝ) : ‖F t‖ ≤ (A * B) * H t := by
      have hL : 0 ≤ Real.log (4 + |t|) + 1 := by
        have hl := Real.log_nonneg (show (1 : ℝ) ≤ 4 + |t| from by linarith only [abs_nonneg t])
        linarith only [hl]
      have hγ := hbA N χ t
      rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, add_comm (1 / 2 : ℂ)] at hγ
      dsimp only [F]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
      calc
        _ ≤ (A * (Real.log (4 + |t|) + 1)) * (B / (1 + t ^ 2)) :=
          mul_le_mul hγ (hbB t) (norm_nonneg _) (mul_nonneg hA.le hL)
        _ = _ := by
          dsimp only [H]; ring
    have hiH : MeasureTheory.Integrable (fun t : ℝ => (A * B) * H t) :=
      Analysis.integrable_log_add_abs_div_one_add_sq.const_mul (A * B)
    have hi :=
      (MeasureTheory.norm_integral_le_integral_norm F).trans
        (MeasureTheory.integral_mono hiF.norm hiH hb)
    rw [MeasureTheory.integral_const_mul] at hi
    change ‖∫ t : ℝ, F t‖ ≤ D at hi
    change ‖d * ∫ t : ℝ, F t‖ ≤ _
    rw [norm_mul]
    exact
      (mul_le_mul_of_nonneg_left (hi.trans (le_max_left D 0)) (norm_nonneg d)).trans
        (le_add_of_nonneg_left zero_le_one)

open AnalyticNumberTheory.DirichletLFunction in
/-- For a nonnegative horizontal interval in the kernel strip below real part three halves,
the weighted gamma logarithmic derivative has vanishing horizontal integrals at signed
heights `n+1`. The universal logarithmic strip bound becomes a logarithm divided by the
height squared after kernel decay. This removes the gamma contour horizontal edges. -/
theorem tendsto_gamma_horizontalIntegral (K : MellinKernel) {N : ℕ} (χ : DirichletCharacter ℂ N)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + K.delta) (hb2 : b ≤ 3 / 2) (hx : 1 ≤ x) (e : ℝ)
    (he : e = 1 ∨ e = -1) :
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
    tendsto_horizontalIntegral_of_scaled_bound K hb (by linarith only [K.delta_pos]) hbK hx
      (fun n => e * T n) (fun n => (Real.log (T n) + D) / (T n) ^ 2)
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
/-- For any character, scale at least one and nonnegative admissible line below three halves,
the gamma Mellin integral equals its central-line integral. The gamma factor and kernel are
regular throughout the intervening strip, so Cauchy gives zero finite boundaries.
Vanishing horizontal integrals and absolute vertical integrability give line independence.
This transfers the uniform central bound to the right integral in the explicit formula. -/
theorem gammaIntegral_eq_central (K : MellinKernel) {N : ℕ} (χ : DirichletCharacter ℂ N) {b x : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 1 / 2 + K.delta) (hb2 : b ≤ 3 / 2) (hx : 1 ≤ x) :
    (∫ t : ℝ,
        logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
          (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      (∫ t : ℝ,
        logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          (K.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))) := by
  let F := fun s : ℂ => logDeriv χ.gammaFactor (s + 1 / 2) * K.function s * (x : ℂ) ^ s
  let T := fun n : ℕ => (n : ℝ) + 1
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hb' : -1 / 2 < b := by linarith only [hb]
  have h0 : (0 : ℝ) ≤ 1 / 2 + K.delta := by linarith only [K.delta_pos]
  have hi0 :=
    integrable_gammaFactor_power_line K χ (c := 0) (by norm_num only) h0 (by norm_num only) hxpos
  have hib := integrable_gammaFactor_power_line K χ hb' hbK hb2 hxpos
  have htop := tendsto_gamma_horizontalIntegral K χ hb hbK hb2 hx 1 (Or.inl rfl)
  have hbot := tendsto_gamma_horizontalIntegral K χ hb hbK hb2 hx (-1) (Or.inr rfl)
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

/-- A kernel-dependent positive constant bounds every right gamma Mellin integral at scale
at least one, uniformly in the modulus, character and admissible nonnegative line below
three halves. Shift the line to the center and apply the proved central bound.
This supplies the bounded archimedean error in the arithmetic explicit formula. -/
theorem exists_norm_gammaIntegral_le (K : MellinKernel) :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) {x b : ℝ},
          1 ≤ x →
            0 ≤ b →
            b ≤ 1 / 2 + K.delta →
            b ≤ 3 / 2 →
            ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
                  (∫ t : ℝ,
                    logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
                      (K.function ((b : ℂ) + Complex.I * t) *
                        (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
              C := by
  obtain ⟨C, hC, hb⟩ := exists_norm_central_gammaIntegral_le K
  refine ⟨C, hC, fun N χ x b hx hb0 hbK hb2 => ?_⟩
  rw [gammaIntegral_eq_central K χ hb0 hbK hb2 hx]
  exact hb N χ (zero_lt_one.trans_le hx)

end PseudoPrime.LLS.PaperStatements.MellinKernel
