/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorVerticalGrowth
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FarLeftReflection

/-!
# Vertical growth of completed logarithmic derivatives

The ordinary Euler series and gamma estimate control the right strip.
The primitive functional equation reflects the left strip to its inverse character.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character and a fixed real part in (1,2], the completed logarithmic
derivative has a logarithmic full-line bound. Bound the ordinary derivative by its
absolutely convergent Mangoldt series and add the gamma-factor bound.
This is the right-strip input to the primitive functional equation. -/
theorem exists_norm_completed_vertical_right_le_log {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ,
          ‖logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)‖ ≤
            A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_norm_logDeriv_gammaFactor_vertical_le_log χ (zero_lt_one.trans hσ) hσ'
  let M := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ
  have hM : 0 ≤ M :=
    tsum_nonneg
      (fun n =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
  refine ⟨B + M, add_pos_of_pos_of_nonneg hB hM, fun t => ?_⟩
  have hr : 1 ≤ ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ.le
  have hp : 0 < ((σ : ℂ) + Complex.I * t).re := zero_lt_one.trans_le hr
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have hc :
    logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t) =
      logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t) +
        logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t) := by
    rw [he]
    ring
  have ho : ‖logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t)‖ ≤ M := by
    have h := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ hσ t
    simpa only [neg_div, norm_neg, logDeriv_apply, mul_comm] using h
  rw [hc]
  have hn :=
    norm_add_le (logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t))
      (logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t))
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  nlinarith only [hn, ho, hb t, hL, hM]

/-- For a primitive nonprincipal character with nonprincipal inverse and fixed real part
in [-1,0), the completed logarithmic derivative has a logarithmic full-line bound.
Reflect to the inverse character's right strip; the conductor contributes a constant.
This gives the left vertical Mellin majorant without GRH. -/
theorem exists_norm_completed_vertical_left_le_log {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : σ < 0) (hσ' : -1 ≤ σ) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ t : ℝ,
          ‖logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)‖ ≤
            A * (Real.log (4 + |t|) + 1) := by
  have hs : 1 < 1 - σ := by linarith only [hσ]
  have hs' : 1 - σ ≤ 2 := by linarith only [hσ']
  obtain ⟨B, hB, hb⟩ := exists_norm_completed_vertical_right_le_log hinv hs hs'
  refine ⟨B + ‖Complex.log (N : ℂ)‖, add_pos_of_pos_of_nonneg hB (norm_nonneg _), fun t => ?_⟩
  let s : ℂ := ((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have hr : 1 ≤ s.re := by
    dsimp only [s]
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hs.le
  have he :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs_eq : 1 - s = (σ : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  rw [hs_eq] at he
  have hn := norm_add_le (Complex.log (N : ℂ)) (logDeriv χ⁻¹.completedLFunction s)
  rw [← he, norm_neg] at hn
  have hbr : ‖logDeriv χ⁻¹.completedLFunction s‖ ≤ B * (Real.log (4 + |t|) + 1) := by
    simpa only [s, abs_neg] using hb (-t)
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  nlinarith only [hn, hbr, hL, norm_nonneg (Complex.log (N : ℂ))]

/-- For a primitive nonprincipal character with nonprincipal inverse and negative real part,
the completed logarithmic derivative is continuous along the whole vertical line.
The functional equation gives nonvanishing from the reflected right half-plane,
so the analytic quotient is continuous. This supplies left-line measurability. -/
theorem continuous_completed_logDeriv_vertical_left {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : σ < 0) :
    Continuous (fun t : ℝ => logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hr : 1 ≤ (1 - ((σ : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    linarith only [hσ]
  have hF := (χ.differentiable_completedLFunction hne).analyticAt ((σ : ℂ) + Complex.I * t)
  have hL : AnalyticAt ℂ (logDeriv χ.completedLFunction) ((σ : ℂ) + Complex.I * t) :=
    hF.deriv.div hF (completedLFunction_ne_zero_farLeft hp hne hinv hr)
  exact
    hL.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + Complex.I * t)
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)

/-- At a fixed real part in (1,2], a positive logarithmic bound for completed logarithmic
derivatives works uniformly for all nonprincipal characters and moduli. Combine the
uniform gamma bound with the absolute Mangoldt series, which depends only on this real
part. This supplies the reflected right-line estimate for conductor errors. -/
theorem exists_uniform_norm_completed_vertical_right_le_log {σ : ℝ} (hσ : 1 < σ) (hσ' : σ ≤ 2) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          χ ≠ 1 →
            ∀ t : ℝ,
              ‖logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)‖ ≤
                A * (Real.log (4 + |t|) + 1) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_uniform_norm_logDeriv_gammaFactor_vertical_le_log (zero_lt_one.trans hσ) hσ'
  let M := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ
  have hM : 0 ≤ M :=
    tsum_nonneg
      (fun n =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ))
  refine ⟨B + M, add_pos_of_pos_of_nonneg hB hM, ?_⟩
  intro N _ χ hne t
  have hr : 1 ≤ ((σ : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hσ.le
  have hp : 0 < ((σ : ℂ) + Complex.I * t).re := zero_lt_one.trans_le hr
  have he :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hne
      (completedLFunction_ne_zero_of_one_le_re hne hr) (gammaFactor_ne_zero_of_re_pos χ hp)
      (analyticAt_gammaFactor_of_re_pos χ hp).differentiableAt
  have hc :
    logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t) =
      logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t) +
        logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t) := by
    rw [he]
    ring
  have ho : ‖logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t)‖ ≤ M := by
    have h := norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ hσ t
    simpa only [neg_div, norm_neg, logDeriv_apply, mul_comm] using h
  rw [hc]
  have hn :=
    norm_add_le (logDeriv χ.LFunction ((σ : ℂ) + Complex.I * t))
      (logDeriv χ.gammaFactor ((σ : ℂ) + Complex.I * t))
  have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  nlinarith only [hn, ho, hb N χ t, hL, hM]

/-- At a fixed real part in [-1,0), a primitive nonprincipal character with nonprincipal
inverse has its completed logarithmic derivative bounded by the norm of the conductor
logarithm plus a logarithmic height term. The latter constant is independent of the
modulus and character. Reflect through the functional equation and apply the uniform
right-line bound. This isolates the conductor dependence of the left Mellin integral. -/
theorem exists_uniform_norm_completed_vertical_left_le_log {σ : ℝ} (hσ : σ < 0) (hσ' : -1 ≤ σ) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
          χ.IsPrimitive →
            χ ≠ 1 →
            χ⁻¹ ≠ 1 →
            ∀ t : ℝ,
              ‖logDeriv χ.completedLFunction ((σ : ℂ) + Complex.I * t)‖ ≤
                ‖Complex.log (N : ℂ)‖ + A * (Real.log (4 + |t|) + 1) := by
  have hs : 1 < 1 - σ := by linarith only [hσ]
  have hs' : 1 - σ ≤ 2 := by linarith only [hσ']
  obtain ⟨B, hB, hb⟩ := exists_uniform_norm_completed_vertical_right_le_log hs hs'
  refine ⟨B, hB, ?_⟩
  intro N _ χ hp hne hinv t
  let s : ℂ := ((1 - σ : ℝ) : ℂ) + Complex.I * ((-t : ℝ) : ℂ)
  have hr : 1 ≤ s.re := by
    dsimp only [s]
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using hs.le
  have he :=
    completedLFunction_logDeriv_functionalEquation_at hp hne
      (completedLFunction_ne_zero_of_one_le_re hinv hr)
  have hs_eq : 1 - s = (σ : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  rw [hs_eq] at he
  have hn := norm_add_le (Complex.log (N : ℂ)) (logDeriv χ⁻¹.completedLFunction s)
  rw [← he, norm_neg] at hn
  have hbr : ‖logDeriv χ⁻¹.completedLFunction s‖ ≤ B * (Real.log (4 + |t|) + 1) := by
    simpa only [s, abs_neg] using hb N χ⁻¹ hinv (-t)
  exact hn.trans (add_le_add_right hbr _)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
