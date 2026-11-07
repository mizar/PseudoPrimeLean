/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDualReflection
public import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedEuler

/-! Reflected Dirichlet series for the asymmetric refined kernel. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Integrate a nonzero reflected Dirichlet coefficient using the inverse-scale
kernel profile. -/
theorem refined_reflected_term_integral (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (((n : ℝ) * x)⁻¹) : ℂ) := by
  have he (t : ℝ) :
    LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
        (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    calc
      _ =
          refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) :=
        by ring
      _ = _ := by
        rw [LLS.PaperStatements.reflected_term_factor f hn hx]
        ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm,
    refined_left_kernel_integral (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)]

/-- The inverse-scale arithmetic term of the reflected sixth-pole kernel,
with zero at index zero. -/
noncomputable def refinedDualTerm (f : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else
    (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (((n : ℝ) * x)⁻¹) : ℂ)

/-- For a positive scale, absolute convergence of the Dirichlet series at
17/16 implies summability of the reflected arithmetic terms. Integrate each
term against the left-line kernel and use the summable integral norm bound. -/
theorem refined_dual_summable {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) : Summable (refinedDualTerm f x) := by
  let W := fun t : ℝ ↦
    refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hiW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip refinedSixPoleKernel (c :=
        (-9 / 16 : ℝ)) (u := x⁻¹)
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) (inv_pos.mpr hx)
    simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
      inv_inv] at h
    exact h
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
    push_cast
    ring
  have hsum :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
        (fun n ↦
          AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
            (fun t : ℝ ↦ -t) continuous_neg W hiW)
        (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
          (fun t : ℝ ↦ -t) W)).summable
  have h := hsum.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  apply h.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero, refinedDualTerm,
      ite_true]
  · simpa only [W, ← he, refinedDualTerm, ite_eq_right hn] using
      refined_reflected_term_integral f hn hx

/-- Absolute Dirichlet convergence permits termwise inversion of the reflected contour integral. -/
theorem refined_reflected_LSeries_integral {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, refinedDualTerm f x n := by
  let W := fun t : ℝ ↦
    refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hd : refinedSixPoleKernel.delta = (1 / 8 : ℝ) := by
    norm_num only [refinedSixPoleKernel, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hiW : MeasureTheory.Integrable W := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip refinedSixPoleKernel (c :=
        (-9 / 16 : ℝ)) (u := x⁻¹)
        (by
          rw [hd]; norm_num only)
        (by
          rw [hd]; norm_num only)
        (by norm_num only) (inv_pos.mpr hx)
    simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
      inv_inv] at h
    exact h
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
    push_cast
    ring
  have hi :=
    AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t) W
      continuous_neg hiW
  simp only [← he] at hi
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) * W t) =
      _
  rw [hi, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero, refinedDualTerm,
      ite_true]
  · simpa only [W, refinedDualTerm, ite_eq_right hn] using refined_reflected_term_integral f hn hx

/-- The reflected logarithmic derivative integral equals the dual Mangoldt series. -/
theorem refined_reflected_logDeriv_integral {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (refinedSixPoleKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, refinedDualTerm (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := refined_reflected_LSeries_integral hx hs
  apply Eq.trans ?_ h
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hre : (1 : ℝ) < (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    norm_num only
  dsimp only
  rw [AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv χ hre]
  simp only [logDeriv, Pi.div_apply, neg_div]

end PseudoPrime.PrimeTestBounds.MillerRabin
