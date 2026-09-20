/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.Arithmetic.MellinWeightedSums
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SmoothedContour

/-!
# Reciprocal weighted character sums as vertical integrals

For any complex Dirichlet character, positive `x`, and `τ > 1`, Mellin inversion of
`mellinWeightOne` identifies the reciprocal weighted sum with the right-vertical integral
of `dirichletReciprocalContourKernel`. Absolute convergence of the von Mangoldt series
and `‖χ n‖ ≤ 1` justify exchanging the sum and integral.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
For a character of nonzero level, `x > 0`, and `τ > 1`, the twisted reciprocal
Mellin-weighted von Mangoldt series equals `(2π)⁻¹` times the vertical kernel integral.
Termwise Mellin inversion and a summable integral-norm majorant justify interchange;
the twisted von Mangoldt Dirichlet series then identifies `-L'/L`.
This supplies the integral identity before collapsing the weight to a finite sum.
-/
theorem characterReciprocalWeightedTerm_tsum_eq_integral {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightOne ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ, dirichletReciprocalContourKernel x χ ((τ : ℂ) + y * Complex.I) := by
  set σ : ℝ := τ - 1 with hσ_def
  have hσ0 : (0 : ℝ) < σ := by
    rw [hσ_def]; linarith
  have hσ1 : σ ≠ -1 := by
    rw [hσ_def]; intro h; linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set K : ℝ → ℂ := fun y ↦ (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I - 1))⁻¹ with hK_def
  have hK_int : MeasureTheory.Integrable K := by
    have hVI := General.verticalIntegrable_mellinReciprocalKernel hσ0.ne' hσ1
    unfold Complex.VerticalIntegrable at hVI
    have heq : (fun y : ℝ ↦ (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1))⁻¹) = K := by
      funext y
      rw [hK_def, hσ_def]
      push_cast
      ring_nf
    rwa [heq] at hVI
  set H : ℕ → ℝ → ℂ := fun n y ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
      (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
      (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) with
    hH_def
  set G : ℕ → ℝ → ℂ := fun n y ↦ K y * H n y with hG_def
  have hnormH :
    ∀ n : ℕ,
      n ≠ 0 →
        ∀ y : ℝ, ‖H n y‖ ≤ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1) := by
    intro n hn y
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_cpow : ‖(n : ℂ) ^ (-((τ : ℂ) + (y : ℂ) * Complex.I))‖ = (n : ℝ) ^ (-τ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      congr 1
      simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
        zero_add]
    have hx_cpow : ‖(x : ℂ) ^ ((τ : ℂ) + (y : ℂ) * Complex.I - 1)‖ = x ^ (τ - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    have hΛ : ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ = ArithmeticFunction.vonMangoldt n := by
      simp only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hχle : ‖χ (n : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    rw [hH_def]
    calc
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
              (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1)‖ =
          ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ * ‖χ (n : ZMod N)‖ *
            ‖(n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))‖ *
            ‖(x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1)‖ :=
        by rw [norm_mul, norm_mul, norm_mul]
      _ ≤ ArithmeticFunction.vonMangoldt n * 1 * (n : ℝ) ^ (-τ) * x ^ (τ - 1) := by
        rw [hΛ, hn_cpow, hx_cpow]
        gcongr
      _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1) := by ring
  -- (1) term-by-term Mellin inversion
  have hterm_raw :
    ∀ n : ℕ,
      n ≠ 0 →
        General.mellinWeightOne ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
                (1 / (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1))) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnx : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
    have hmellin := General.mellinInv_mellinWeightOne_eq (σ := σ) (x := (n : ℝ) / x) hσ0 hnx
    rw [← hmellin]
    simp only [mellinInv, smul_eq_mul, one_div]
  have hterm :
    ∀ n : ℕ,
      n ≠ 0 →
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * χ (n : ZMod N) *
            General.mellinWeightOne ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [hterm_raw n hn, mul_smul_comm]
    congr 1
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    simp only [hG_def, hH_def, hK_def]
    rw [General.cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg, one_div, Complex.ofReal_natCast]
    have hshift : ((τ : ℂ) + y * Complex.I - 1) = (σ : ℂ) + y * Complex.I := by
      rw [hσ_def]; push_cast; ring
    have hshift' : ((σ : ℂ) + y * Complex.I + 1) = (τ : ℂ) + y * Complex.I := by
      rw [hσ_def]; push_cast; ring
    rw [hshift, hshift']
    rw [show (-((σ : ℂ) + y * Complex.I)) = 1 + -((τ : ℂ) + y * Complex.I) by
        rw [hσ_def]; push_cast; ring,
      Complex.cpow_add _ _ hnC, Complex.cpow_one]
    field_simp [hnC]
  -- (2) each `G n` is integrable, dominated by a constant multiple of `K`
  have hGint : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hG0 : G 0 = fun _ ↦ (0 : ℂ) := by
        funext y
        simp only [hG_def, hH_def, neg_add_rev, ArithmeticFunction.map_zero, Complex.ofReal_zero,
          Nat.cast_zero, zero_mul, CharP.cast_eq_zero, mul_zero]
      rw [hG0]
      exact MeasureTheory.integrable_zero _ _ _
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      apply hK_int.mul_bdd
      · have hline : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hHcont : Continuous (H n) := by
          rw [hH_def]
          exact
            ((continuous_const.mul continuous_const).mul (hline.neg.const_cpow (Or.inl hnC))).mul
              ((hline.sub continuous_const).const_cpow (Or.inl hxC))
        exact hHcont.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y ↦ hnormH n hn y
  -- (3) the `L¹` norms of `G n` are summable, via the `‖χ n‖ ≤ 1` majorant
  have hGnorm_le :
    ∀ n : ℕ,
      n ≠ 0 →
        ∫ y : ℝ, ‖G n y‖ ≤
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ∫ y : ℝ, ‖K y‖ := by
    intro n hn
    have hcongr :
      ∀ y : ℝ,
        ‖G n y‖ ≤ (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ‖K y‖ := by
      intro y
      rw [hG_def, norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hnormH n hn y) (norm_nonneg _)
    calc
      ∫ y : ℝ, ‖G n y‖ ≤
          ∫ y : ℝ, (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ‖K y‖ :=
        MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hK_int.norm.const_mul _) (Filter.Eventually.of_forall hcongr)
      _ = (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ∫ y : ℝ, ‖K y‖ := by
        rw [MeasureTheory.integral_const_mul]
  have hSummableL : Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖G n y‖) := by
    have hΛ_summable :
      Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ)) := by
      have hLS :
        Summable
          (fun n : ℕ ↦
            ‖LSeries.term (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (τ : ℂ) n‖) :=
        summable_norm_iff.mpr
          (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (τ : ℂ))
            (by simpa only [Complex.ofReal_re] using hτ))
      refine hLS.congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
          zero_mul]
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [LSeries.term_def]
        simp only [hn, ite_false]
        rw [norm_div, show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg hnpos.le, div_eq_mul_inv]
    have hΛx_summable := hΛ_summable.mul_right (x ^ (τ - 1) * ∫ y : ℝ, ‖K y‖)
    have hnn : ∀ n : ℕ, 0 ≤ ∫ y : ℝ, ‖G n y‖ := fun n =>
      MeasureTheory.integral_nonneg fun y => norm_nonneg _
    apply Summable.of_nonneg_of_le hnn _ hΛx_summable
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hG0 : G 0 = fun _ ↦ (0 : ℂ) := by
        funext y
        simp only [hG_def, hH_def, neg_add_rev, ArithmeticFunction.map_zero, Complex.ofReal_zero,
          Nat.cast_zero, zero_mul, CharP.cast_eq_zero, mul_zero]
      rw [hG0]
      simp only [norm_zero, MeasureTheory.integral_zero, ArithmeticFunction.map_zero,
        CharP.cast_eq_zero, zero_mul, Std.le_refl]
    · calc
        ∫ y : ℝ, ‖G n y‖ ≤
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ∫ y : ℝ, ‖K y‖ :=
          hGnorm_le n hn
        _ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * (x ^ (τ - 1) * ∫ y : ℝ, ‖K y‖) := by
          ring
  -- (4) exchange the sum and the integral
  have hInterchange := MeasureTheory.hasSum_integral_of_summable_integral_norm hGint hSummableL
  have hsum_eq_integral : ∑' n : ℕ, ∫ y : ℝ, G n y = ∫ y : ℝ, ∑' n : ℕ, G n y :=
    hInterchange.tsum_eq
  -- (5) identify the inner sum over `n` with the primitive reciprocal contour kernel
  have hinner :
    ∀ y : ℝ, ∑' n : ℕ, G n y = dirichletReciprocalContourKernel x χ ((τ : ℂ) + y * Complex.I) := by
    intro y
    have hs : (1 : ℝ) < ((τ : ℂ) + y * Complex.I).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
      linarith
    have hLS := lSeries_twist_vonMangoldt_eq_neg_logDeriv_dirichletLFunction_of_one_lt_re χ hs
    have hsum :
      ∑' n : ℕ,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
            (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) =
        -deriv (DirichletCharacter.LFunction χ) ((τ : ℂ) + y * Complex.I) /
          DirichletCharacter.LFunction χ ((τ : ℂ) + y * Complex.I) := by
      rw [← hLS]
      unfold LSeries
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, Nat.cast_zero, zero_mul,
          CharP.cast_eq_zero, neg_add_rev, LSeries.term_zero]
      · rw [LSeries.term_def]
        simp only [hn, ite_false, div_eq_mul_inv, Complex.cpow_neg]
        ring
    calc
      ∑' n : ℕ, G n y =
          ∑' n : ℕ,
            K y *
              ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
                (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) :=
        by
        refine tsum_congr fun n ↦ ?_
        rw [hG_def, hH_def]
        ring
      _ =
          K y *
            (∑' n : ℕ,
              (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N) *
                (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) :=
        by rw [tsum_mul_right, tsum_mul_left]
      _ = dirichletReciprocalContourKernel x χ ((τ : ℂ) + y * Complex.I) := by
        rw [hsum, hK_def]
        unfold dirichletReciprocalContourKernel
        simp only [div_eq_mul_inv]
        ring
  -- assemble
  have hLHS :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * χ (n : ZMod N) *
          General.mellinWeightOne ((n : ℝ) / x) =
      ∑' n : ℕ, (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero, div_zero,
        Nat.cast_zero, zero_mul, zero_div, mul_inv_rev, hG_def, hH_def, neg_add_rev, mul_zero,
        MeasureTheory.integral_zero, smul_zero]
    · exact hterm n hn
  rw [hLHS, tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹, hsum_eq_integral]
  congr 1
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)

/--
For any character of nonzero level, `x > 0`, and `τ > 1`, the finite reciprocal
weighted character sum equals `(2π)⁻¹` times the right-vertical kernel integral.
Combine the finite-sum collapse with `characterReciprocalWeightedTerm_tsum_eq_integral`.
This identifies the right edge in the reciprocal contour limit.
-/
theorem characterReciprocalWeightedSum_eq_integral {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    (Arithmetic.characterReciprocalWeightedSum x χ : ℂ) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ, dirichletReciprocalContourKernel x χ ((τ : ℂ) + y * Complex.I) := by
  rw [← Arithmetic.characterReciprocalWeightedTerm_tsum_eq χ hx,
    characterReciprocalWeightedTerm_tsum_eq_integral χ hx hτ]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
