/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.UnconditionalGenusBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound

/-! # Unconditional good-height horizontal contour estimates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character and any scale at least one, choose one
height, radius, and positive ordinate separation controlling both signs of the
centered logarithmic derivative and nonvanishing on the growing real strip.
The genus estimate uses the finite unconditional inverse-square mass instead of
the RH-specific closed form. This supplies the good-height witnesses needed for
unconditional horizontal contour limits on every fixed rectangle. -/
theorem exists_primitiveHorizontalScaledStripLogDerivBound_unconditionally {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
    ∃ T ∈ Set.Icc n (2 * n),
      ∃ R ∈ Set.Icc (8 * n) (16 * n),
        ∃ δ : ℝ,
          0 < δ ∧
            δ =
              n /
                (8 *
                  (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2 +
                    1)) ∧
            ∀ σ : ℝ,
              |σ| ≤ 2 * n →
                ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + T * Complex.I) -
                        logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
                    192 * ‖(σ : ℂ) + T * Complex.I‖ *
                          ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                            1) /
                        R ^ 2 +
                      2 * ‖(σ : ℂ) + T * Complex.I‖ / R ^ 2 *
                        (Real.log
                            (max 1 (completedLFunctionBallBound N (2 * R)) /
                              ‖DirichletCharacter.completedLFunction χ 0‖) /
                          Real.log 2) +
                      ‖(σ : ℂ) + T * Complex.I‖ *
                          Real.sqrt (completedLFunctionInverseSquareMass χ) *
                          Real.sqrt
                            (Real.log
                                (max 1 (completedLFunctionBallBound N (2 * R)) /
                                  ‖DirichletCharacter.completedLFunction χ 0‖) /
                              Real.log 2) /
                        δ ∧
                  ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) - T * Complex.I) -
                        logDeriv (DirichletCharacter.completedLFunction χ) 0‖ ≤
                    192 * ‖(σ : ℂ) - T * Complex.I‖ *
                          ((4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
                              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                            1) /
                        R ^ 2 +
                      2 * ‖(σ : ℂ) - T * Complex.I‖ / R ^ 2 *
                        (Real.log
                            (max 1 (completedLFunctionBallBound N (2 * R)) /
                              ‖DirichletCharacter.completedLFunction χ 0‖) /
                          Real.log 2) +
                      ‖(σ : ℂ) - T * Complex.I‖ *
                          Real.sqrt (completedLFunctionInverseSquareMass χ) *
                          Real.sqrt
                            (Real.log
                                (max 1 (completedLFunctionBallBound N (2 * R)) /
                                  ‖DirichletCharacter.completedLFunction χ 0‖) /
                              Real.log 2) /
                        δ ∧
                  DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
                  DirichletCharacter.completedLFunction χ ((σ : ℂ) - T * Complex.I) ≠ 0 := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  obtain ⟨T, hT, hTgood⟩ :=
    exists_primitiveGoodHeightRadius_twoSided hN1 hprimitive hne hinv hn
      (show 2 * n ≤ 16 * n by nlinarith only [hn])
  obtain ⟨R, hR, hRgood⟩ :=
    exists_primitiveGoodRadius hN1 hprimitive hne hinv (show (1 : ℝ) ≤ 8 * n by nlinarith only [hn])
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num only) hn
  rw [show (2 : ℝ) * (8 * n) = 16 * n from by ring] at hR hRgood
  set δ :=
    n /
      (8 *
        (Real.log
              (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2 +
          1)) with
    hδ_def
  have hBnonnegT :
    (0 : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 :=
    le_trans (Nat.cast_nonneg _)
      (card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv
        (show (0 : ℝ) < 16 * n by exact mul_pos (by norm_num only) hnpos))
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    exact div_pos hnpos (mul_pos (by norm_num only) (by linarith only [hBnonnegT]))
  refine ⟨T, hT, R, hR, δ, hδ_pos, hδ_def, ?_⟩
  have hTle : T ≤ 2 * n := hT.2
  have hTge : n ≤ T := hT.1
  have hRle : R ≤ 16 * n := hR.2
  have hRge : 8 * n ≤ R := hR.1
  have hRge1 : (1 : ℝ) ≤ R := by nlinarith only [hRge, hn]
  have hzf : ∀ ρ : ℂ, ‖ρ‖ = R → DirichletCharacter.completedLFunction χ ρ ≠ 0 := by
    intro ρ hρR hζ
    have hρle : ‖ρ‖ ≤ 16 * n := hρR ▸ hRle
    have hmargin := hRgood ρ hζ hρle
    rw [hρR, sub_self, abs_zero] at hmargin
    have hcardR :=
      card_primitiveZeroNormsInBall_le hN1 hprimitive hne hinv
        (show (0 : ℝ) < 2 * (8 * n) by
          exact mul_pos (by norm_num only) (mul_pos (by norm_num only) hnpos))
    rw [show (2 : ℝ) * (2 * (8 * n)) = 4 * (8 * n) from by ring] at hcardR
    have hBnonnegR :
      (0 : ℝ) ≤
        Real.log
            (max 1 (completedLFunctionBallBound N (4 * (8 * n))) /
              ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 :=
      le_trans (Nat.cast_nonneg _) hcardR
    have hmargin_pos :
      0 <
        8 * n /
          (4 *
            (Real.log
                  (max 1 (completedLFunctionBallBound N (4 * (8 * n))) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2 +
              1)) := by
      exact
        div_pos (mul_pos (by norm_num only) hnpos)
          (mul_pos (by norm_num only) (by linarith only [hBnonnegR]))
    linarith only [hmargin, hmargin_pos]
  intro σ hσ
  have hnorm_bound : ∀ T' : ℝ, |T'| = T → ‖(σ : ℂ) + T' * Complex.I‖ ≤ |σ| + T := by
    intro T' hT'
    have h1 : ‖(σ : ℂ) + T' * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(T' : ℂ) * Complex.I‖ := norm_add_le _ _
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] at h1
    rwa [hT'] at h1
  have hplus_sim : ((σ : ℂ) + T * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
  have hminus_sim : ((σ : ℂ) - T * Complex.I).im = -T := by
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      mul_one, Complex.I_re, mul_zero, add_zero, zero_sub]
  have hplus_le : ‖(σ : ℂ) + T * Complex.I‖ ≤ R / 2 := by
    have :=
      hnorm_bound T
        (abs_of_nonneg (by exact le_trans (by norm_num only : (0 : ℝ) ≤ 1) (le_trans hn hTge)))
    linarith only [this, hσ, hTle, hRge, hn]
  have hminus_le : ‖(σ : ℂ) - T * Complex.I‖ ≤ R / 2 := by
    have h1 : ‖(σ : ℂ) - T * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(T : ℂ) * Complex.I‖ := by
      have h2 := norm_sub_le (σ : ℂ) ((T : ℂ) * Complex.I)
      exact h2
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] at h1
    rw [abs_of_nonneg
        (show (0 : ℝ) ≤ T by
          exact le_trans (by norm_num only : (0 : ℝ) ≤ 1) (le_trans hn hTge))] at h1
    linarith only [h1, hσ, hTle, hRge, hn]
  have hplus_le16n : ‖(σ : ℂ) + T * Complex.I‖ ≤ 16 * n := by linarith only [hplus_le, hRle, hn]
  have hminus_le16n : ‖(σ : ℂ) - T * Complex.I‖ ≤ 16 * n := by linarith only [hminus_le, hRle, hn]
  have hplus_sne : DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * Complex.I) ≠ 0 := by
    intro hζs
    have hmargin := (hTgood ((σ : ℂ) + T * Complex.I) hζs hplus_le16n).1
    rw [hplus_sim, sub_self, abs_zero] at hmargin
    linarith only [hδ_pos, hmargin]
  have hminus_sne : DirichletCharacter.completedLFunction χ ((σ : ℂ) - T * Complex.I) ≠ 0 := by
    intro hζs
    have hmargin := (hTgood ((σ : ℂ) - T * Complex.I) hζs hminus_le16n).2
    rw [hminus_sim] at hmargin
    have : T + -T = 0 := by ring
    rw [this, abs_zero] at hmargin
    linarith only [hδ_pos, hmargin]
  have hplus_sep :
    ∀ ρ : ℂ,
      DirichletCharacter.completedLFunction χ ρ = 0 →
        ‖ρ‖ < R → δ ≤ ‖(σ : ℂ) + T * Complex.I - ρ‖ := by
    intro ρ hζ hρR
    have hρle : ‖ρ‖ ≤ 16 * n := le_trans hρR.le hRle
    have hmargin := (hTgood ρ hζ hρle).1
    calc
      δ ≤ |T - ρ.im| := hmargin
      _ = |((σ : ℂ) + T * Complex.I).im - ρ.im| := by rw [hplus_sim]
      _ = |((σ : ℂ) + T * Complex.I - ρ).im| := by rw [Complex.sub_im]
      _ ≤ ‖(σ : ℂ) + T * Complex.I - ρ‖ := Complex.abs_im_le_norm _
  have hminus_sep :
    ∀ ρ : ℂ,
      DirichletCharacter.completedLFunction χ ρ = 0 →
        ‖ρ‖ < R → δ ≤ ‖(σ : ℂ) - T * Complex.I - ρ‖ := by
    intro ρ hζ hρR
    have hρle : ‖ρ‖ ≤ 16 * n := le_trans hρR.le hRle
    have hmargin := (hTgood ρ hζ hρle).2
    calc
      δ ≤ |T + ρ.im| := hmargin
      _ = |((σ : ℂ) - T * Complex.I).im - ρ.im| := by
        rw [hminus_sim, show -T - ρ.im = -(T + ρ.im) from by ring, abs_neg]
      _ = |((σ : ℂ) - T * Complex.I - ρ).im| := by simp only [Complex.sub_im]
      _ ≤ ‖(σ : ℂ) - T * Complex.I - ρ‖ := Complex.abs_im_le_norm _
  exact
    ⟨norm_centeredLogDeriv_le_of_separation_unconditionally hN2 hprimitive hne hinv hRge1 hzf
        hplus_le hplus_sne hδ_pos hplus_sep,
      norm_centeredLogDeriv_le_of_separation_unconditionally hN2 hprimitive hne hinv hRge1 hzf
        hminus_le hminus_sne hδ_pos hminus_sep,
      hplus_sne, hminus_sne⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
