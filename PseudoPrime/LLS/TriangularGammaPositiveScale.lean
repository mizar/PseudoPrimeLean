/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MellinKernelGammaPositiveScale
public import PseudoPrime.LLS.TriangularScaledGammaBounds
public import PseudoPrime.LLS.TriangularGammaWeightSeries

/-!
# Triangular Gamma evaluations at every positive scale

Transfer the central weight series, uniform bound and exterior zero value to admissible
right lines. These results apply to both scales of the exact dual-scale formula.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For every character and positive scale, the normalized alpha-18 Gamma integral
on any line between zero and five eighths has norm at most 6000. Shift to the center
and apply the raw bound 34848. This also bounds the inverse-scale Gamma term. -/
theorem triangular18_gammaIntegral_norm_le_six_thousand_of_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      (6000 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.gammaIntegral_eq_central_of_pos K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) hx
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * _‖ ≤ _
  rw [he]
  have hraw := triangular18_central_gammaIntegral_norm_le_scaled_decay χ hx
  have hn := norm_mellinNormalization_mul_le_sixth hraw
  exact hn.trans (by norm_num only : (34848 : ℝ) / 6 ≤ 6000)

/-- For every character and positive scale below exp(-36), the normalized alpha-18
Gamma integral on an admissible right line vanishes. Transfer the central weight-series
zero evaluation along the positive-scale contour shift. No GRH is required. -/
theorem triangular18_gammaIntegral_eq_zero_of_small_scale {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 0 < x) (hsmall : x < Real.exp (-36)) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      0 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.gammaIntegral_eq_central_of_pos K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = 0
  rw [he]
  exact
    triangular_central_gammaIntegral_eq_zero_of_small_scale χ (by norm_num only : (0 : ℝ) < 18) hx
      (by
        norm_num only at hsmall ⊢; exact hsmall)

/-- For every character and scale above exp(36), the inverse-scale normalized
alpha-18 Gamma integral vanishes on every admissible right line. Invert the positive
scale inequality and apply the small-scale zero theorem in the dual-scale formula. -/
theorem triangular18_inverse_gammaIntegral_eq_zero_of_large_scale {q : ℕ}
    (χ : DirichletCharacter ℂ q) {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : Real.exp 36 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function ((b : ℂ) + Complex.I * t) * (x⁻¹ : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
      0 := by
  have hxpos : 0 < x := (Real.exp_pos 36).trans hx
  have hs : x⁻¹ < Real.exp (-36) := by
    rw [Real.exp_neg]
    exact inv_lt_inv₀ hxpos (Real.exp_pos 36) |>.mpr hx
  simpa only [Complex.ofReal_inv] using
    triangular18_gammaIntegral_eq_zero_of_small_scale χ hb hbK (inv_pos.mpr hxpos) hs

/-- For every character, a parity base between one quarter and one evaluates the
normalized alpha-18 Gamma integral on every admissible right line and positive scale
as the baseline profile plus half the convergent reciprocal-weight series. Shift to
the center and use its explicit series. This covers the interior inverse-scale branch. -/
theorem triangular18_gammaIntegral_eq_weight_series {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ β : ℝ,
      1 / 4 ≤ β ∧
        β ≤ 1 ∧
          ∀ (b x : ℝ),
            0 ≤ b →
              b ≤ 5 / 8 →
                0 < x →
                  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
                  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                      (∫ t : ℝ,
                        logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
                          (K.function ((b : ℂ) + Complex.I * t) *
                            (x : ℂ) ^ ((b : ℂ) + Complex.I * t))) =
                    ((-Complex.log Real.pi + Complex.digamma (β : ℂ)) / 2) *
                        (triangularKernelProfile 18 x : ℂ) +
                      (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm 18 (β + n) x := by
  obtain ⟨β, hβ, hβ1, hg⟩ := triangular_central_gammaIntegral_eq_weight_series χ
  refine ⟨β, hβ, hβ1, ?_⟩
  intro b x hb hbK hx
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.gammaIntegral_eq_central_of_pos K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) hx
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * _ = _
  rw [he]
  exact hg 18 x (by norm_num only) hx

end PseudoPrime.LLS.PaperStatements
