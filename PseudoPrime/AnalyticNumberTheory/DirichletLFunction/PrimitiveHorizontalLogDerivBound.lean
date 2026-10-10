/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardLimit
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GoodHeight
public import PseudoPrime.AnalyticNumberTheory.General.LogPolynomialDecay

/-!
# Coarse subquadratic bound on the horizontal-edge log-derivative

This is a coarse bound on
`‖logDeriv (completedLFunction χ) s‖` on a horizontal line `Im s = T` at a good height `T`, coarse
enough (`O(T^{3/2}(log T)^{3/2})`, not the sharp `O((log T)²)` ζ-side bound) to make the horizontal
contour edge vanish as `T → ∞`.

`DirichletLFunction.norm_centeredLogDeriv_sub_truncatedGenus_le` theorem only bounds the
*difference* between the centered log-derivative and the truncated genus sum
`DirichletLFunction.completedLFunctionTruncatedGenusSum χ R s`; the genus sum itself is bounded
here via a weighted
Cauchy–Schwarz argument: writing `1/(s-ρ)+1/ρ = s/(ρ(s-ρ))` termwise and
applying Cauchy–Schwarz with weight `m_ρ` to the two factors `1/|ρ|` and `1/|s-ρ|` gives

`Σ m_ρ/(|ρ||s-ρ|) ≤ √(Σ m_ρ/|ρ|²) · √(Σ m_ρ/|s-ρ|²)`.

The first factor is the inverse-square zero mass `2|Re B(χ)|` (an `R`-independent constant); the
second is
bounded by `(zero count in `ball 0 R`)/δ²` using the good-height margin `δ` between `Im s` and every
zero ordinate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-! ### the strip argument instantiation at a good height/radius pair -/

/-! ### A single `T, R, δ` for every `σ` on both horizontal edges -/

/-- Under RH for this primitive nonprincipal character and n>=1, select one good height,
radius and positive ordinate separation that control both signed completed logarithmic
derivatives and nonvanishing on the growing strip |Re s|<=2n. The inverse-square mass
requires only this character's RH; good-height and radius selection require no RH.
This covers every fixed shifted rectangle once n is sufficiently large. -/
theorem exists_primitiveHorizontalScaledStripLogDerivBound_of_dirichletRH {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
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
                      ‖(σ : ℂ) + T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
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
                      ‖(σ : ℂ) - T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
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
    positivity
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
      positivity
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
    ⟨norm_centeredLogDeriv_le_of_separation_of_dirichletRH hN2 hRH hprimitive hne hinv hRge1 hzf
        hplus_le hplus_sne hδ_pos hplus_sep,
      norm_centeredLogDeriv_le_of_separation_of_dirichletRH hN2 hRH hprimitive hne hinv hRge1 hzf
        hminus_le hminus_sne hδ_pos hminus_sep,
      hplus_sne, hminus_sne⟩

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and `n ≥ 1`, choose a single
`T ∈ [n,2n]`, `R ∈ [8n,16n]`, and the displayed positive margin `δ` such that the bounds
and completed-function nonvanishing hold at both `σ+Ti` and `σ-Ti` for every `|σ| ≤ 2`.
Proof: two-sided good-height selection protects both signs of zero ordinates up to radius
`16n`; good-radius selection makes the sphere zero-free. The height and radius ranges imply
`‖σ±Ti‖ ≤ R/2`, and each ordinate margin bounds the corresponding complex distance.
Role: retains a common height and nonvanishing for integration along both horizontal edges.
-/
theorem exists_primitiveHorizontalStripLogDerivBound_with_nonzero {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
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
              |σ| ≤ 2 →
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
                      ‖(σ : ℂ) + T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
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
                      ‖(σ : ℂ) - T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                          Real.sqrt
                            (Real.log
                                (max 1 (completedLFunctionBallBound N (2 * R)) /
                                  ‖DirichletCharacter.completedLFunction χ 0‖) /
                              Real.log 2) /
                        δ ∧
                  DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
                  DirichletCharacter.completedLFunction χ ((σ : ℂ) - T * Complex.I) ≠ 0 := by
  obtain ⟨T, hT, R, hR, δ, hδpos, hδeq, hall⟩ :=
    exists_primitiveHorizontalScaledStripLogDerivBound_of_dirichletRH hN2 (hGRH N χ hprimitive)
      hprimitive hne hinv hn
  refine ⟨T, hT, R, hR, δ, hδpos, hδeq, ?_⟩
  intro σ hσ
  exact hall σ (by linarith only [hσ, hn])

/-! ### the horizontal pointwise bound: bundling the strip argument strip witness -/

/--
A good-height witness at scale `n` for the completed logarithmic derivative.
Fields `T,R,δ` are the height, radius, and positive separation margin; `T_mem,R_mem`
place them in `[n,2n]` and `[8n,16n]`, and `δ_eq` fixes the explicit margin.
The `bound` and `nonzero` fields hold for every `|σ| ≤ 2` at both signs of the height.
This packages the uniform strip theorem for the chosen height sequence.
-/
structure PrimitiveHorizontalStripData {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℝ) where
  /-- The good height. -/
  T : ℝ
  /-- The good radius. -/
  R : ℝ
  /-- The margin. -/
  δ : ℝ
  /-- The height lies between the scale and twice the scale. -/
  T_mem : T ∈ Set.Icc n (2 * n)
  /-- The radius lies between eight and sixteen times the scale. -/
  R_mem : R ∈ Set.Icc (8 * n) (16 * n)
  /-- Strict positivity permits division by the separation margin. -/
  δ_pos : 0 < δ
  /-- The explicit two-sided margin determined by the zero-count bound at radius `16n`. -/
  δ_eq :
    δ =
      n /
        (8 *
          (Real.log
                (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2 +
            1))
  /-- Uniform centered-logarithmic-derivative estimates at both signs of the chosen height. -/
  bound :
    ∀ σ : ℝ,
      |σ| ≤ 2 →
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
              ‖(σ : ℂ) + T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
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
              ‖(σ : ℂ) - T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                  Real.sqrt
                    (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * R)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2) /
                δ
  /-- Nonvanishing at both signs of the height, uniformly for `|σ| ≤ 2`.
  The completed-to-ordinary logarithmic-derivative bridge uses this alongside `bound`. -/
  nonzero :
    ∀ σ : ℝ,
      |σ| ≤ 2 →
        DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
          DirichletCharacter.completedLFunction χ ((σ : ℂ) - T * Complex.I) ≠ 0

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, `χ⁻¹ ≠ 1`, and `n ≥ 1`, select height,
radius, and explicit positive margin from the uniform two-sided strip theorem.
The returned `PrimitiveHorizontalStripData χ n` stores both centered-derivative estimates
and nonvanishing for all `|σ| ≤ 2`. Role: packages choices for the general height sequence.
-/
noncomputable def primitiveHorizontalStripData {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
    PrimitiveHorizontalStripData χ n := by
  choose T hT R hR δ hδpos hδeq hall using
    exists_primitiveHorizontalStripLogDerivBound_with_nonzero hN2 hGRH hprimitive hne hinv hn
  exact
    ⟨T, R, δ, hT, hR, hδpos, hδeq, fun σ hσ => ⟨(hall σ hσ).1, (hall σ hσ).2.1⟩, fun σ hσ =>
      (hall σ hσ).2.2⟩

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, select strip data at
scale `n = k+1`. Nonnegativity of the natural index ensures `n ≥ 1`.
Role: supplies heights, radii, margins, and uniform bounds for the general-character sequence limit.
-/
noncomputable def primitiveHorizontalStripDataSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) :
    PrimitiveHorizontalStripData χ ((k : ℝ) + 1) :=
  primitiveHorizontalStripData hN2 hGRH hprimitive hne hinv
    (by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith only [this])

/-! ### the horizontal pointwise bound: an explicit `O(X log X)` envelope for the intermediate
bound's log-bound -/

/--
For `N ≥ 2`, a primitive nontrivial character and `X ≥ 1`, the Jensen
logarithmic ball bound is at most the displayed explicit `O(X log X)` envelope.
Use the exponential ball bound, absorb the maximum with one, and expand
the logarithm of the quotient. This makes horizontal-strip estimates explicit.
-/
theorem H2LogBound_le_explicit {N : ℕ} [NeZero N] (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {X : ℝ} (hX : 1 ≤ X) :
    Real.log
          (max 1 (completedLFunctionBallBound N X) / ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 ≤
      ((4 * (N : ℝ) + 3) * (X + 3) * Real.log (X + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 := by
  have hF0pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have hlogX3nonneg : 0 ≤ Real.log (X + 3) := Real.log_nonneg (by nlinarith only [hX])
  have hexpnonneg : (0 : ℝ) ≤ (4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3)) := by positivity
  have hexp_ge1 : (1 : ℝ) ≤ Real.exp ((4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3))) := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr hexpnonneg
  have hexp := completedLFunctionBallBound_le_exp (N := N) hN2 hX
  have hmax_le :
    max 1 (completedLFunctionBallBound N X) ≤
      Real.exp ((4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3))) :=
    max_le hexp_ge1 hexp
  have hmaxpos : (0 : ℝ) < max 1 (completedLFunctionBallBound N X) := lt_max_of_lt_left one_pos
  have hdiv_le :
    max 1 (completedLFunctionBallBound N X) / ‖DirichletCharacter.completedLFunction χ 0‖ ≤
      Real.exp ((4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3))) /
        ‖DirichletCharacter.completedLFunction χ 0‖ := by
    gcongr
  have hlog_le :
    Real.log
        (max 1 (completedLFunctionBallBound N X) / ‖DirichletCharacter.completedLFunction χ 0‖) ≤
      Real.log
        (Real.exp ((4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3))) /
          ‖DirichletCharacter.completedLFunction χ 0‖) :=
    Real.log_le_log (by positivity) hdiv_le
  have hrhs_eq :
    Real.log
        (Real.exp ((4 * (N : ℝ) + 3) * ((X + 3) * Real.log (X + 3))) /
          ‖DirichletCharacter.completedLFunction χ 0‖) =
      (4 * (N : ℝ) + 3) * (X + 3) * Real.log (X + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
    rw [Real.log_div (by positivity) hF0pos.ne', Real.log_exp]
    ring
  rw [hrhs_eq] at hlog_le
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  gcongr

/--
Input/assumptions: `2 ≤ N`, a primitive nontrivial character.
Conclusion: there is a fixed positive constant `K` (depending only on `N`, `χ`) such that,
eventually as `n → ∞`, `H2LogBound_le_explicit`'s envelope at `X = 32n` is at most `K · n · log n`.
Content: no sharp constant is needed. `32n + 3 ≤
35n` (`n ≥ 1`) and `log(35n) = log 35 + log n ≤ (log 35 + 1) log n` (`n ≥ e`, so `log n ≥ 1`) give
`(32n+3)log(32n+3) ≤ 35(log 35 + 1) n log n`; absorbing the fixed `-log‖F 0‖` term into a doubled
constant (once `n` is large enough that the main term dominates it) finishes it.
Role: bounds the zero-count expression at radius `32n` in the
`K n log n` shape `General.tendsto_sqrt_mul_add_one_div_sq_atTop` consumes.
-/
theorem exists_K_forall_H2LogBound_thirtyTwo_le {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ᶠ n : ℝ in Filter.atTop,
          ((4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2 ≤
            K * n * Real.log n := by
  have hF0pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  set C₁ : ℝ := Real.log 35 + 1 with hC1_def
  have hC1pos : 0 < C₁ := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 35 by norm_num only)
    rw [hC1_def]
    linarith only [this]
  set K : ℝ := 2 * (4 * (N : ℝ) + 3) * 35 * C₁ / Real.log 2 with hK_def
  have hKpos : 0 < K := by
    rw [hK_def]
    positivity
  have hlog35pos : 0 < Real.log 35 := Real.log_pos (by norm_num only)
  have hC1gt1 : 1 < C₁ := by
    rw [hC1_def]
    linarith only [hlog35pos]
  refine ⟨K, hKpos, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_ge_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (|Real.log ‖DirichletCharacter.completedLFunction χ 0‖|)] with n hnE
    hn1 hnF0
  have hn0 : (0 : ℝ) < n := by exact lt_of_lt_of_le (Real.exp_pos (1 : ℝ)) hnE
  have hlogn_ge1 : (1 : ℝ) ≤ Real.log n := by
    rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
    exact Real.log_le_log (Real.exp_pos 1) hnE
  have hlognpos : 0 < Real.log n := lt_of_lt_of_le (by norm_num only) hlogn_ge1
  have h35n : 32 * n + 3 ≤ 35 * n := by nlinarith only [hn1]
  have hlog35n : Real.log (32 * n + 3) ≤ Real.log (35 * n) :=
    Real.log_le_log (by nlinarith only [hn1]) h35n
  have hlog35n_eq : Real.log (35 * n) = Real.log 35 + Real.log n := by
    rw [Real.log_mul (by norm_num only) hn0.ne']
  have hlog35n_le : Real.log (32 * n + 3) ≤ C₁ * Real.log n := by
    rw [hC1_def]
    have : Real.log 35 + Real.log n ≤ (Real.log 35 + 1) * Real.log n := by
      nlinarith only [hlogn_ge1, Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 35)]
    linarith only [hlog35n, hlog35n_eq, this]
  have hmain_le : (32 * n + 3) * Real.log (32 * n + 3) ≤ 35 * n * (C₁ * Real.log n) := by
    apply
      mul_le_mul h35n hlog35n_le (Real.log_nonneg (by nlinarith only [hn1]))
        (mul_nonneg (by norm_num only) hn0.le)
  have hmain_pos : 0 < 35 * n * (C₁ * Real.log n) := by positivity
  have h35C1log : (1 : ℝ) ≤ 35 * C₁ * Real.log n := by nlinarith only [hC1gt1, hlogn_ge1]
  have hF0bound :
    -Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤ 35 * n * (C₁ * Real.log n) := by
    have h1 : -Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤ n := by
      calc
        -Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
            |Real.log ‖DirichletCharacter.completedLFunction χ 0‖| :=
          neg_le_abs _
        _ ≤ n := hnF0
    nlinarith only [h1, h35C1log, hn0.le]
  have hsum_le :
    (4 * (N : ℝ) + 3) * ((32 * n + 3) * Real.log (32 * n + 3)) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
      2 * (4 * (N : ℝ) + 3) * (35 * n * (C₁ * Real.log n)) := by
    have h1 :
      (4 * (N : ℝ) + 3) * ((32 * n + 3) * Real.log (32 * n + 3)) ≤
        (4 * (N : ℝ) + 3) * (35 * n * (C₁ * Real.log n)) := by
      apply mul_le_mul_of_nonneg_left hmain_le (by positivity)
    nlinarith only [h1, hF0bound, hmain_pos]
  rw [div_le_iff₀ hlog2pos]
  have hKcancel :
    K * n * Real.log n * Real.log 2 = 2 * (4 * (N : ℝ) + 3) * 35 * C₁ * n * Real.log n := by
    rw [hK_def]
    field_simp [ne_of_gt hlog2pos]
  rw [hKcancel]
  nlinarith only [hsum_le]

/-- the intermediate bound's error coefficient `(4N+3)(R+3)log(R+3) - log‖F 0‖ + 1` (appearing in
the finite-radius estimate / the strip argument strip
bound's first term) is always positive, not just eventually: comparing `‖F 0‖` to the ball bound
at radius `R` (as inside `DirichletLFunction.norm_logDeriv_ecanonicalDecomp_sub_le`'s own proof)
gives
`log‖F 0‖ ≤ (4N+3)(R+3)log(R+3)`, so adding `1` keeps it strictly positive. -/
theorem hadamardHorizontalErrorCoeff_pos {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ}
    (hR : 1 ≤ R) :
    0 <
      (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
        1 := by
  have hN1 : 1 < N := hN2
  have hF0pos : (0 : ℝ) < ‖DirichletCharacter.completedLFunction χ 0‖ :=
    norm_pos_iff.mpr (dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne)
  have h0R : ‖(0 : ℂ)‖ ≤ R := by
    rw [norm_zero]
    exact le_trans (by norm_num only) hR
  have hboundge : ‖DirichletCharacter.completedLFunction χ 0‖ ≤ completedLFunctionBallBound N R :=
    norm_completedLFunction_le_completedLFunctionBallBound hN1 hprimitive hne hinv
      (le_trans (by norm_num only) hR) h0R
  have hboundpos : (0 : ℝ) < completedLFunctionBallBound N R := hF0pos.trans_le hboundge
  have hbound_exp := completedLFunctionBallBound_le_exp (N := N) hN2 hR
  have hlog_bound_le :
    Real.log (completedLFunctionBallBound N R) ≤
      (4 * (N : ℝ) + 3) * (R + 3) * Real.log (R + 3) := by
    have hlog := Real.log_le_log hboundpos hbound_exp
    rw [Real.log_exp] at hlog
    calc
      Real.log (completedLFunctionBallBound N R) ≤
          (4 * (N : ℝ) + 3) * ((R + 3) * Real.log (R + 3)) :=
        hlog
      _ = _ := by ring
  have hlogF0_le_bound :
    Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
      Real.log (completedLFunctionBallBound N R) :=
    Real.log_le_log hF0pos hboundge
  linarith only [hlog_bound_le, hlogF0_le_bound]

/-- the intermediate bound's log-bound is always nonnegative, via the underlying zero-count
cardinality (reused from
the height-selection argument's `DirichletLFunction.card_primitiveZeroOrdinatesInBall_le`, whose
LHS is a `Finset.card` cast to `ℝ`). -/
theorem H2LogBound_nonneg {N : ℕ} [NeZero N] (hN1 : 1 < N) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {R : ℝ} (hR : 0 < R) :
    (0 : ℝ) ≤
      Real.log
          (max 1 (completedLFunctionBallBound N (2 * R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 :=
  le_trans (Nat.cast_nonneg _) (card_primitiveZeroOrdinatesInBall_le hN1 hprimitive hne hinv hR)

/-! ### the horizontal pointwise bound: the strip argument genus-sum term's core new asymptotic
fact -/

/-! ### Assembly of the height-normalized horizontal estimate -/

/--
For GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, define the real envelope at
`n = k+1` using `primitiveHorizontalStripDataSeq`'s chosen height, radius, and margin.
Its numerator replaces `‖σ±Ti‖` by `4n` in the three centered-derivative bound terms;
division by `T²` gives a bound independent of `σ` for the normalized horizontal edges.
Role: the subsequent bounds and squeeze theorem prove this envelope tends to zero.
-/
noncomputable def primitiveHorizontalStripEpsilon {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) : ℝ :=
  let n : ℝ := (k : ℝ) + 1
  let d := primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k
  (768 * n *
          ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
            1) /
        d.R ^ 2 +
      8 * n *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) /
        d.R ^ 2 +
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        d.δ) /
    d.T ^ 2

/--
Under GRH, for `N ≥ 2`, a primitive nontrivial character with nontrivial inverse,
and `|σ| ≤ 2`, both signed-height normalized logarithmic derivative bounds
are at most `primitiveHorizontalStripEpsilon`. Bound the evaluation-point norm
by the selected height scale and use nonnegativity of each coefficient.
This gives the uniform error bounds needed for the horizontal limit.
-/
theorem primitiveHorizontalStripEpsilon_bound {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {σ : ℝ} (hσ : |σ| ≤ 2) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) +
                  (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T ^ 2 ≤
        primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k ∧
      ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) -
                  (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T ^ 2 ≤
        primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  set n : ℝ := (k : ℝ) + 1 with hn_def
  set d := primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k with hd_def
  have hnge1 : (1 : ℝ) ≤ n := by
    rw [hn_def]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith only [this]
  have hTge : n ≤ d.T := d.T_mem.1
  have hTle : d.T ≤ 2 * n := d.T_mem.2
  have hRge : 8 * n ≤ d.R := d.R_mem.1
  have hRle : d.R ≤ 16 * n := d.R_mem.2
  have hTpos : 0 < d.T := lt_of_lt_of_le (by norm_num only) (le_trans hnge1 hTge)
  have hRpos : 0 < d.R :=
    lt_of_lt_of_le (by norm_num only) (le_trans (by nlinarith only [hnge1] : (1 : ℝ) ≤ 8 * n) hRge)
  have hAR_pos :=
    hadamardHorizontalErrorCoeff_pos hN2 hprimitive hne hinv
      (show (1 : ℝ) ≤ d.R by nlinarith only [hRge, hnge1])
  have hBR_nonneg := H2LogBound_nonneg hN1 hprimitive hne hinv hRpos
  have hRsq_pos : (0 : ℝ) < d.R ^ 2 := by positivity
  have hTsq_pos : (0 : ℝ) < d.T ^ 2 := by positivity
  have hδpos := d.δ_pos
  have hsplus_le : ‖(σ : ℂ) + d.T * Complex.I‖ ≤ 4 * n := by
    have h1 : ‖(σ : ℂ) + d.T * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(d.T : ℂ) * Complex.I‖ := norm_add_le _ _
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] at h1
    rw [abs_of_nonneg
        (show (0 : ℝ) ≤ d.T by
          exact le_trans (by norm_num only : (0 : ℝ) ≤ 1) (le_trans hnge1 hTge))] at h1
    linarith only [h1, hσ, hTle, hnge1]
  have hsminus_le : ‖(σ : ℂ) - d.T * Complex.I‖ ≤ 4 * n := by
    have h1 : ‖(σ : ℂ) - d.T * Complex.I‖ ≤ ‖(σ : ℂ)‖ + ‖(d.T : ℂ) * Complex.I‖ := norm_sub_le _ _
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one] at h1
    rw [abs_of_nonneg
        (show (0 : ℝ) ≤ d.T by
          exact le_trans (by norm_num only : (0 : ℝ) ≤ 1) (le_trans hnge1 hTge))] at h1
    linarith only [h1, hσ, hTle, hnge1]
  obtain ⟨hplus, hminus⟩ := d.bound σ hσ
  have hkey :
    ∀ s : ℂ,
      ‖s‖ ≤ 4 * n →
        192 * ‖s‖ *
                ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                    Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                  1) /
              d.R ^ 2 +
            2 * ‖s‖ / d.R ^ 2 *
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) +
            ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                Real.sqrt
                  (Real.log
                      (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2) /
              d.δ ≤
          768 * n *
                ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                    Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                  1) /
              d.R ^ 2 +
            8 * n *
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
              d.R ^ 2 +
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
                Real.sqrt
                  (Real.log
                      (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2) /
              d.δ := by
    intro s hs
    have hsnonneg : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
    have hE1num :
      192 * ‖s‖ *
          ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
            1) ≤
        768 * n *
          ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
            1) := by
      have hscale : 192 * ‖s‖ ≤ 768 * n := by linarith only [hs]
      exact mul_le_mul_of_nonneg_right hscale hAR_pos.le
    have hE1 :
      192 * ‖s‖ *
            ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          d.R ^ 2 ≤
        768 * n *
            ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
              1) /
          d.R ^ 2 := by
      gcongr
    have hE2num :
      2 * ‖s‖ *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) ≤
        8 * n *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) := by
      have hscale : 2 * ‖s‖ ≤ 8 * n := by linarith only [hs]
      exact mul_le_mul_of_nonneg_right hscale hBR_nonneg
    have hE2 :
      2 * ‖s‖ / d.R ^ 2 *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) ≤
        8 * n *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
          d.R ^ 2 := by
      have heq :
        2 * ‖s‖ / d.R ^ 2 *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) =
          2 * ‖s‖ *
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) *
            (d.R ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        ring
      rw [heq, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right hE2num (inv_nonneg.mpr hRsq_pos.le)
    have hE3 :
      ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          d.δ ≤
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
          d.δ := by
      have h1 : ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) ≤ 4 * n * Real.sqrt (2 * |primitiveBRe χ|) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
      have h2 :
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) ≤
          4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
            Real.sqrt
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
      have hδinv_nonneg : (0 : ℝ) ≤ d.δ⁻¹ := inv_nonneg.mpr hδpos.le
      calc
        ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                Real.sqrt
                  (Real.log
                      (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2) /
              d.δ =
            ‖s‖ * Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) *
              d.δ⁻¹ :=
          div_eq_mul_inv _ _
        _ ≤
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) *
              d.δ⁻¹ :=
          mul_le_mul_of_nonneg_right h2 hδinv_nonneg
        _ =
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
                Real.sqrt
                  (Real.log
                      (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                        ‖DirichletCharacter.completedLFunction χ 0‖) /
                    Real.log 2) /
              d.δ :=
          (div_eq_mul_inv _ _).symm
    linarith only [hE1, hE2, hE3]
  refine ⟨?_, ?_⟩
  · calc
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + d.T * Complex.I) -
                logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
            d.T ^ 2 ≤
          (192 * ‖(σ : ℂ) + d.T * Complex.I‖ *
                  ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                      Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                    1) /
                d.R ^ 2 +
              2 * ‖(σ : ℂ) + d.T * Complex.I‖ / d.R ^ 2 *
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) +
              ‖(σ : ℂ) + d.T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                  Real.sqrt
                    (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2) /
                d.δ) /
            d.T ^ 2 :=
        by gcongr
      _ ≤ primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k := by
        change
          _ ≤
            (768 * n *
                    ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                      1) /
                  d.R ^ 2 +
                8 * n *
                    (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2) /
                  d.R ^ 2 +
                4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
                    Real.sqrt
                      (Real.log
                          (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                            ‖DirichletCharacter.completedLFunction χ 0‖) /
                        Real.log 2) /
                  d.δ) /
              d.T ^ 2
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hkey _ hsplus_le) (inv_nonneg.mpr hTsq_pos.le)
  · calc
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) - d.T * Complex.I) -
                logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
            d.T ^ 2 ≤
          (192 * ‖(σ : ℂ) - d.T * Complex.I‖ *
                  ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                      Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                    1) /
                d.R ^ 2 +
              2 * ‖(σ : ℂ) - d.T * Complex.I‖ / d.R ^ 2 *
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) +
              ‖(σ : ℂ) - d.T * Complex.I‖ * Real.sqrt (2 * |primitiveBRe χ|) *
                  Real.sqrt
                    (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2) /
                d.δ) /
            d.T ^ 2 :=
        by gcongr
      _ ≤ primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k := by
        change
          _ ≤
            (768 * n *
                    ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                      1) /
                  d.R ^ 2 +
                8 * n *
                    (Real.log
                        (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                          ‖DirichletCharacter.completedLFunction χ 0‖) /
                      Real.log 2) /
                  d.R ^ 2 +
                4 * n * Real.sqrt (2 * |primitiveBRe χ|) *
                    Real.sqrt
                      (Real.log
                          (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                            ‖DirichletCharacter.completedLFunction χ 0‖) /
                        Real.log 2) /
                  d.δ) /
              d.T ^ 2
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right (hkey _ hsminus_le) (inv_nonneg.mpr hTsq_pos.le)

/-! ### The explicit `n`-dependent envelope and its limit -/

/--
The explicit `n`-dependent majorant for the height-normalized strip error.
Its terms result from bounding the ball-count expression by `K*n*log n` and using
the chosen height and radius ranges. For fixed `K > 0` it tends to zero.
-/
noncomputable def primitiveHorizontalStripCleanEnvelope {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (K : ℝ) (n : ℝ) : ℝ :=
  12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 + K / 8 * Real.log n / n ^ 2 +
    32 * Real.sqrt (2 * |primitiveBRe χ|) *
        (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
      n ^ 2

/-- **The clean envelope's limit**: `primitiveHorizontalStripCleanEnvelope K n → 0` as `n → ∞`, for
any fixed `K > 0`. Each of the four additive terms `→ 0`: the first three via
`General.tendsto_log_div_sq_atTop`/`n⁻³ → 0`, the fourth (genus term) via the core new asymptotic
fact
`PseudoPrime.AnalyticNumberTheory.General.tendsto_sqrt_mul_add_one_div_sq_atTop`. -/
theorem tendsto_primitiveHorizontalStripCleanEnvelope_atTop {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {K : ℝ} (hK : 0 < K) :
    Filter.Tendsto (fun n : ℝ => primitiveHorizontalStripCleanEnvelope (N := N) (χ := χ) K n)
      Filter.atTop (nhds 0) := by
  have hinv3 : Filter.Tendsto (fun n : ℝ => (n ^ 3)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num only))
  have hterm1 :
    Filter.Tendsto (fun n : ℝ => 12 * Real.log 2 * K * Real.log n / n ^ 2) Filter.atTop
      (nhds 0) := by
    have := General.tendsto_log_div_sq_atTop.const_mul (12 * Real.log 2 * K)
    simpa only [mul_div_assoc, mul_zero] using this
  have hterm2 : Filter.Tendsto (fun n : ℝ => 12 / n ^ 3) Filter.atTop (nhds 0) := by
    have := hinv3.const_mul (12 : ℝ)
    simpa only [div_eq_mul_inv, mul_zero] using this
  have hterm3 : Filter.Tendsto (fun n : ℝ => K / 8 * Real.log n / n ^ 2) Filter.atTop (nhds 0) := by
    have := General.tendsto_log_div_sq_atTop.const_mul (K / 8)
    simpa only [mul_div_assoc, mul_zero] using this
  have hterm4 :
    Filter.Tendsto
      (fun n : ℝ =>
        32 * Real.sqrt (2 * |primitiveBRe χ|) *
            (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
          n ^ 2)
      Filter.atTop (nhds 0) := by
    have hcore := General.tendsto_sqrt_mul_add_one_div_sq_atTop K hK
    have := hcore.const_mul (32 * Real.sqrt (2 * |primitiveBRe χ|))
    simpa only [Nat.ofNat_nonneg, Real.sqrt_mul, mul_assoc, mul_div_assoc, mul_zero] using this
  have hsum := ((hterm1.add hterm2).add hterm3).add hterm4
  rw [show (0 : ℝ) + 0 + 0 + 0 = 0 from by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards with n
  unfold primitiveHorizontalStripCleanEnvelope
  ring

/-! ### Eventual comparison with the explicit envelope -/

/--
Input/assumptions: same as `primitiveHorizontalStripEpsilon_bound`.
Conclusion: there is a fixed `K > 0` such that eventually (`k → ∞`),
`primitiveHorizontalStripEpsilon ... k ≤ primitiveHorizontalStripCleanEnvelope K (k + 1)`.
Content: worst-cases `B_R := H2LogBound(2R)` and `B₃₂ := H2LogBound(32n)` (`d.δ`'s underlying
bound) both by `K n log n` (via `H2LogBound_le_explicit` +
`General.add_three_mul_log_add_three_mono` +
`exists_K_forall_H2LogBound_thirtyTwo_le`'s eventual bound, composed from `ℝ` to `ℕ` via
`Filter.Tendsto.eventually`), and `A_R` by `(log 2) K n log n + 1`; substitutes these into
`primitiveHorizontalStripEpsilon`'s three terms using `R ≥ 8n`, `T ≥ n`.
Role: supplies the eventual comparison for the generic-character squeeze argument.
-/
theorem eventually_primitiveHorizontalStripEpsilon_le_cleanEnvelope {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ᶠ k : ℕ in Filter.atTop,
          primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k ≤
            primitiveHorizontalStripCleanEnvelope (χ := χ) K ((k : ℝ) + 1) := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  obtain ⟨K, hKpos, hKevent⟩ := exists_K_forall_H2LogBound_thirtyTwo_le hN2 hprimitive hne
  refine ⟨K, hKpos, ?_⟩
  have hnn_tendsto : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have hKevent_k := hnn_tendsto.eventually hKevent
  filter_upwards [hKevent_k] with k hk
  set n : ℝ := (k : ℝ) + 1 with hn_def
  set d := primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k with hd_def
  have hnge1 : (1 : ℝ) ≤ n := by
    rw [hn_def]
    have := Nat.cast_nonneg (α := ℝ) k
    linarith only [this]
  have hTge : n ≤ d.T := d.T_mem.1
  have hRge : 8 * n ≤ d.R := d.R_mem.1
  have hRle : d.R ≤ 16 * n := d.R_mem.2
  have hTpos : 0 < d.T := lt_of_lt_of_le (by norm_num only) (le_trans hnge1 hTge)
  have hRpos : 0 < d.R :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (le_trans (by nlinarith only [hnge1]) hRge)
  have hTsq_pos : (0 : ℝ) < d.T ^ 2 := by positivity
  have hRsq_pos : (0 : ℝ) < d.R ^ 2 := by positivity
  have hnpos : 0 < n := lt_of_lt_of_le (by norm_num only) hnge1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num only)
  have hAR_pos :=
    hadamardHorizontalErrorCoeff_pos hN2 hprimitive hne hinv
      (show (1 : ℝ) ≤ d.R by nlinarith only [hRge, hnge1])
  have hlogn_nonneg : 0 ≤ Real.log n := Real.log_nonneg hnge1
  have hKnlogn_nonneg : (0 : ℝ) ≤ K * n * Real.log n := by positivity
  -- B_R ≤ K n log n
  have hBR_le :
    Real.log
          (max 1 (completedLFunctionBallBound N (2 * d.R)) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 ≤
      K * n * Real.log n := by
    have h1 :=
      H2LogBound_le_explicit hN2 hprimitive hne
        (show (1 : ℝ) ≤ 2 * d.R by nlinarith only [hRge, hnge1])
    have h2 : (2 * d.R + 3) * Real.log (2 * d.R + 3) ≤ (32 * n + 3) * Real.log (32 * n + 3) :=
      General.add_three_mul_log_add_three_mono
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hRpos.le) (by nlinarith only [hRle, hnge1])
    have hnum :
      (4 * (N : ℝ) + 3) * (2 * d.R + 3) * Real.log (2 * d.R + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
        (4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ := by
      have hcoef : (0 : ℝ) ≤ 4 * (N : ℝ) + 3 := by positivity
      have hmul := mul_le_mul_of_nonneg_left h2 hcoef
      calc
        _ =
            (4 * (N : ℝ) + 3) * ((2 * d.R + 3) * Real.log (2 * d.R + 3)) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ :=
          by ring
        _ ≤
            (4 * (N : ℝ) + 3) * ((32 * n + 3) * Real.log (32 * n + 3)) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ :=
          sub_le_sub_right hmul _
        _ = _ := by ring
    have h3 :
      ((4 * (N : ℝ) + 3) * (2 * d.R + 3) * Real.log (2 * d.R + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 ≤
        ((4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
            Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
          Real.log 2 := by
      gcongr
    exact h1.trans (h3.trans hk)
  -- B₃₂ (underlying δ's bound) ≤ K n log n
  have hB32_le :
    Real.log
          (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
            ‖DirichletCharacter.completedLFunction χ 0‖) /
        Real.log 2 ≤
      K * n * Real.log n := by
    have h1 :=
      H2LogBound_le_explicit hN2 hprimitive hne
        (show (1 : ℝ) ≤ 2 * (16 * n) by nlinarith only [hnge1])
    rw [show (2 : ℝ) * (16 * n) = 32 * n from by ring] at h1 ⊢
    exact h1.trans hk
  -- A_R ≤ (log 2) K n log n + 1
  have hAR_le :
    (4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
        1 ≤
      Real.log 2 * (K * n * Real.log n) + 1 := by
    have h2 : (d.R + 3) * Real.log (d.R + 3) ≤ (32 * n + 3) * Real.log (32 * n + 3) :=
      General.add_three_mul_log_add_three_mono hRpos.le (by nlinarith only [hRle, hnge1])
    have hcoef : (0 : ℝ) ≤ 4 * (N : ℝ) + 3 := by positivity
    have hnum :
      (4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) ≤
        (4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) := by
      have hmul := mul_le_mul_of_nonneg_left h2 hcoef
      calc
        _ = (4 * (N : ℝ) + 3) * ((d.R + 3) * Real.log (d.R + 3)) := by ring
        _ ≤ (4 * (N : ℝ) + 3) * ((32 * n + 3) * Real.log (32 * n + 3)) := hmul
        _ = _ := by ring
    have hk' :
      (4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
          Real.log ‖DirichletCharacter.completedLFunction χ 0‖ ≤
        Real.log 2 * (K * n * Real.log n) := by
      have := mul_le_mul_of_nonneg_left hk hlog2pos.le
      rw [show
          Real.log 2 *
              (((4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
                  Real.log ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) =
            (4 * (N : ℝ) + 3) * (32 * n + 3) * Real.log (32 * n + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖
          from by field_simp [ne_of_gt hlog2pos]] at this
      linarith only [this]
    linarith only [hnum, hk']
  -- 1/δ ≤ 8*(K n log n + 1)/n
  have hδinv_le : d.δ⁻¹ ≤ 8 * (K * n * Real.log n + 1) / n := by
    rw [d.δ_eq, inv_div]
    have hnum :
      8 *
          (Real.log
                (max 1 (completedLFunctionBallBound N (2 * (16 * n))) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2 +
            1) ≤
        8 * (K * n * Real.log n + 1) := by
      linarith only [hB32_le]
    gcongr
  set AR :=
    (4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
        Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
      1 with
    hAR_def
  set BR :=
    Real.log
        (max 1 (completedLFunctionBallBound N (2 * d.R)) /
          ‖DirichletCharacter.completedLFunction χ 0‖) /
      Real.log 2 with
    hBR_def
  change
    (768 * n * AR / d.R ^ 2 + 8 * n * BR / d.R ^ 2 +
          4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ) /
        d.T ^ 2 ≤
      12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 + K / 8 * Real.log n / n ^ 2 +
        32 * Real.sqrt (2 * |primitiveBRe χ|) *
            (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
          n ^ 2
  have hR2 : (64 : ℝ) * n ^ 2 ≤ d.R ^ 2 := by
    have hn8 : (0 : ℝ) ≤ 8 * n := mul_nonneg (by norm_num only) hnpos.le
    have hsq := mul_self_le_mul_self hn8 hRge
    calc
      64 * n ^ 2 = (8 * n) * (8 * n) := by ring
      _ ≤ d.R * d.R := hsq
      _ = d.R ^ 2 := by ring
  have hT2 : n ^ 2 ≤ d.T ^ 2 := by
    have hsq := mul_self_le_mul_self hnpos.le hTge
    calc
      n ^ 2 = n * n := by ring
      _ ≤ d.T * d.T := hsq
      _ = d.T ^ 2 := by ring
  have hARnonneg : 0 ≤ AR := hAR_pos.le
  have hBRnonneg : 0 ≤ BR := H2LogBound_nonneg hN1 hprimitive hne hinv hRpos
  have hdenom_swap : ∀ a : ℝ, 0 ≤ a → a / d.R ^ 2 / d.T ^ 2 ≤ a / (64 * n ^ 4) := by
    intro a ha
    rw [div_div]
    have hd : (64 : ℝ) * n ^ 4 ≤ d.R ^ 2 * d.T ^ 2 := by
      have := mul_le_mul hR2 hT2 (by positivity) (by positivity)
      calc
        64 * n ^ 4 = (64 * n ^ 2) * n ^ 2 := by ring
        _ ≤ d.R ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right hR2 (sq_nonneg n)
        _ ≤ d.R ^ 2 * d.T ^ 2 := mul_le_mul_of_nonneg_left hT2 (sq_nonneg d.R)
    have hpos : (0 : ℝ) < 64 * n ^ 4 := mul_pos (by norm_num only) (pow_pos hnpos 4)
    calc
      a / (d.R ^ 2 * d.T ^ 2) = a * (d.R ^ 2 * d.T ^ 2)⁻¹ := div_eq_mul_inv _ _
      _ ≤ a * (64 * n ^ 4)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ hpos hd) ha
      _ = a / (64 * n ^ 4) := (div_eq_mul_inv _ _).symm
  have hTdenom_swap : ∀ a : ℝ, 0 ≤ a → a / d.T ^ 2 ≤ a / n ^ 2 := by
    intro a ha
    calc
      a / d.T ^ 2 = a * (d.T ^ 2)⁻¹ := div_eq_mul_inv _ _
      _ ≤ a * (n ^ 2)⁻¹ := mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hT2) ha
      _ = a / n ^ 2 := (div_eq_mul_inv _ _).symm
  have hterm1 :
    768 * n * AR / d.R ^ 2 / d.T ^ 2 ≤ 12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 := by
    have hstep1 : 768 * n * AR / d.R ^ 2 / d.T ^ 2 ≤ 768 * n * AR / (64 * n ^ 4) :=
      hdenom_swap (768 * n * AR) (mul_nonneg (mul_nonneg (by norm_num only) hnpos.le) hARnonneg)
    have heq1 : 768 * n * AR / (64 * n ^ 4) = 12 * AR / n ^ 3 := by
      field_simp [ne_of_gt hnpos]
      ring
    have hstep2 : 12 * AR / n ^ 3 ≤ 12 * (Real.log 2 * (K * n * Real.log n) + 1) / n ^ 3 := by
      have hnum : 12 * AR ≤ 12 * (Real.log 2 * (K * n * Real.log n) + 1) := by
        linarith only [hAR_le]
      gcongr
    have heq2 :
      12 * (Real.log 2 * (K * n * Real.log n) + 1) / n ^ 3 =
        12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 := by
      field_simp [ne_of_gt hnpos]
    calc
      768 * n * AR / d.R ^ 2 / d.T ^ 2 ≤ 768 * n * AR / (64 * n ^ 4) := hstep1
      _ = 12 * AR / n ^ 3 := heq1
      _ ≤ 12 * (Real.log 2 * (K * n * Real.log n) + 1) / n ^ 3 := hstep2
      _ = 12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 := heq2
  have hterm2 : 8 * n * BR / d.R ^ 2 / d.T ^ 2 ≤ K / 8 * Real.log n / n ^ 2 := by
    have hstep1 : 8 * n * BR / d.R ^ 2 / d.T ^ 2 ≤ 8 * n * BR / (64 * n ^ 4) :=
      hdenom_swap (8 * n * BR) (mul_nonneg (mul_nonneg (by norm_num only) hnpos.le) hBRnonneg)
    have heq1 : 8 * n * BR / (64 * n ^ 4) = BR / (8 * n ^ 3) := by
      field_simp [ne_of_gt hnpos]
      ring
    have hstep2 : BR / (8 * n ^ 3) ≤ K * n * Real.log n / (8 * n ^ 3) := by gcongr
    have heq2 : K * n * Real.log n / (8 * n ^ 3) = K / 8 * Real.log n / n ^ 2 := by
      field_simp [ne_of_gt hnpos]
    calc
      8 * n * BR / d.R ^ 2 / d.T ^ 2 ≤ 8 * n * BR / (64 * n ^ 4) := hstep1
      _ = BR / (8 * n ^ 3) := heq1
      _ ≤ K * n * Real.log n / (8 * n ^ 3) := hstep2
      _ = K / 8 * Real.log n / n ^ 2 := heq2
  have hterm3 :
    4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ / d.T ^ 2 ≤
      32 * Real.sqrt (2 * |primitiveBRe χ|) *
          (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
        n ^ 2 := by
    have hsqrtBR_le : Real.sqrt BR ≤ Real.sqrt (K * n * Real.log n) := Real.sqrt_le_sqrt hBR_le
    have hδpos := d.δ_pos
    have hbase_nonneg : 0 ≤ 4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ := by
      positivity
    have hstep0 :
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ ≤
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) / d.δ := by
      have h1 :
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR ≤
          4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) :=
        mul_le_mul_of_nonneg_left hsqrtBR_le (by positivity)
      calc
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ =
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR * d.δ⁻¹ :=
          div_eq_mul_inv _ _
        _ ≤ 4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) * d.δ⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr hδpos.le)
        _ = 4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) / d.δ :=
          (div_eq_mul_inv _ _).symm
    have hstep1 :
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) / d.δ ≤
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) *
          (8 * (K * n * Real.log n + 1) / n) := by
      have hbase2_nonneg :
        0 ≤ 4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) := by
        positivity
      calc
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) / d.δ =
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) * d.δ⁻¹ :=
          div_eq_mul_inv _ _
        _ ≤
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) *
              (8 * (K * n * Real.log n + 1) / n) :=
          mul_le_mul_of_nonneg_left hδinv_le hbase2_nonneg
    have heq1 :
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) *
          (8 * (K * n * Real.log n + 1) / n) =
        32 * Real.sqrt (2 * |primitiveBRe χ|) *
          (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) := by
      field_simp [ne_of_gt hnpos]
      ring
    have hcombine :
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ ≤
        32 * Real.sqrt (2 * |primitiveBRe χ|) *
          (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) := by
      calc
        4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ ≤
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) / d.δ :=
          hstep0
        _ ≤
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt (K * n * Real.log n) *
              (8 * (K * n * Real.log n + 1) / n) :=
          hstep1
        _ =
            32 * Real.sqrt (2 * |primitiveBRe χ|) *
              (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) :=
          heq1
    calc
      4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ / d.T ^ 2 ≤
          (4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ) / n ^ 2 :=
        hTdenom_swap _ hbase_nonneg
      _ ≤
          (32 * Real.sqrt (2 * |primitiveBRe χ|) *
              (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1))) /
            n ^ 2 :=
        by gcongr
  have hnum := add_le_add (add_le_add hterm1 hterm2) hterm3
  calc
    (768 * n * AR / d.R ^ 2 + 8 * n * BR / d.R ^ 2 +
            4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ) /
          d.T ^ 2 =
        768 * n * AR / d.R ^ 2 / d.T ^ 2 + 8 * n * BR / d.R ^ 2 / d.T ^ 2 +
          4 * n * Real.sqrt (2 * |primitiveBRe χ|) * Real.sqrt BR / d.δ / d.T ^ 2 :=
      by ring
    _ ≤
        (12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 + K / 8 * Real.log n / n ^ 2) +
          32 * Real.sqrt (2 * |primitiveBRe χ|) *
              (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
            n ^ 2 :=
      hnum
    _ =
        12 * Real.log 2 * K * Real.log n / n ^ 2 + 12 / n ^ 3 + K / 8 * Real.log n / n ^ 2 +
          32 * Real.sqrt (2 * |primitiveBRe χ|) *
              (Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1)) /
            n ^ 2 :=
      by ring

/-! ### Convergence by squeezing the general-character envelope -/

/-- `primitiveHorizontalStripEpsilon` is always `≥ 0` (each of its three terms is a
nonnegative numerator over a positive denominator). -/
theorem primitiveHorizontalStripEpsilon_nonneg {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) :
    0 ≤ primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  set d := primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k with hd_def
  have hnge1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith only [this]
  have hRge : 8 * ((k : ℝ) + 1) ≤ d.R := d.R_mem.1
  have hTge : (k : ℝ) + 1 ≤ d.T := d.T_mem.1
  have hRpos : 0 < d.R :=
    lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1) (le_trans (by nlinarith only [hnge1]) hRge)
  have hTpos : 0 < d.T := lt_of_lt_of_le (by norm_num only) (le_trans hnge1 hTge)
  have hAR_pos :=
    hadamardHorizontalErrorCoeff_pos hN2 hprimitive hne hinv
      (show (1 : ℝ) ≤ d.R by nlinarith only [hRge, hnge1])
  have hBR_nonneg := H2LogBound_nonneg hN1 hprimitive hne hinv hRpos
  have hδpos := d.δ_pos
  change
    (0 : ℝ) ≤
      (768 * ((k : ℝ) + 1) *
              ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
                  Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
                1) /
            d.R ^ 2 +
          8 * ((k : ℝ) + 1) *
              (Real.log
                  (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                    ‖DirichletCharacter.completedLFunction χ 0‖) /
                Real.log 2) /
            d.R ^ 2 +
          4 * ((k : ℝ) + 1) * Real.sqrt (2 * |primitiveBRe χ|) *
              Real.sqrt
                (Real.log
                    (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                      ‖DirichletCharacter.completedLFunction χ 0‖) /
                  Real.log 2) /
            d.δ) /
        d.T ^ 2
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) + 1 := le_trans (by norm_num only) hnge1
  have hR2_nonneg : (0 : ℝ) ≤ d.R ^ 2 := (sq_pos_of_pos hRpos).le
  have hT2_nonneg : (0 : ℝ) ≤ d.T ^ 2 := (sq_pos_of_pos hTpos).le
  have hterm1 :
    0 ≤
      768 * ((k : ℝ) + 1) *
          ((4 * (N : ℝ) + 3) * (d.R + 3) * Real.log (d.R + 3) -
              Real.log ‖DirichletCharacter.completedLFunction χ 0‖ +
            1) /
        d.R ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hk_nonneg) hAR_pos.le) hR2_nonneg
  have hterm2 :
    0 ≤
      8 * ((k : ℝ) + 1) *
          (Real.log
              (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                ‖DirichletCharacter.completedLFunction χ 0‖) /
            Real.log 2) /
        d.R ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hk_nonneg) hBR_nonneg) hR2_nonneg
  have hterm3 :
    0 ≤
      4 * ((k : ℝ) + 1) * Real.sqrt (2 * |primitiveBRe χ|) *
          Real.sqrt
            (Real.log
                (max 1 (completedLFunctionBallBound N (2 * d.R)) /
                  ‖DirichletCharacter.completedLFunction χ 0‖) /
              Real.log 2) /
        d.δ :=
    div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num only) hk_nonneg) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
      hδpos.le
  exact div_nonneg (add_nonneg (add_nonneg hterm1 hterm2) hterm3) hT2_nonneg

/-- **The generic horizontal estimate limit**: `primitiveHorizontalStripEpsilon ... k → 0`
as `k → ∞`.
Combines the eventual clean-envelope domination
(`eventually_primitiveHorizontalStripEpsilon_le_cleanEnvelope`), the clean envelope's own
limit (`tendsto_primitiveHorizontalStripCleanEnvelope_atTop`), and nonnegativity, via
`tendsto_of_tendsto_of_tendsto_of_le_of_le'` (squeeze with `Eventually` bounds on both sides). -/
theorem tendsto_primitiveHorizontalStripEpsilon_atTop {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv) Filter.atTop
      (nhds 0) := by
  obtain ⟨K, hKpos, hKle⟩ :=
    eventually_primitiveHorizontalStripEpsilon_le_cleanEnvelope hN2 hGRH hprimitive hne hinv
  have hq := tendsto_primitiveHorizontalStripCleanEnvelope_atTop (N := N) (χ := χ) hKpos
  have hnn_tendsto : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have hqk :
    Filter.Tendsto
      (fun k : ℕ => primitiveHorizontalStripCleanEnvelope (N := N) (χ := χ) K ((k : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    hq.comp hnn_tendsto
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hqk
      (Filter.Eventually.of_forall
        (primitiveHorizontalStripEpsilon_nonneg hN2 hGRH hprimitive hne hinv))
      hKle

/-! ### General-character height-sequence limit -/

/-! ### Named general-character height sequence -/

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, return the chosen height
at scale `k+1` from `primitiveHorizontalStripDataSeq`.
The output lies in `[k+1,2(k+1)]`, with uniform centered-derivative bounds and nonvanishing
on both strips. Role: names the general-character height sequence for horizontal contour limits.
-/
noncomputable def primitiveHorizontalHeightSeq {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) : ℝ :=
  (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T

/--
For the primitive-character GRH data, the chosen height at index `k` is at least `k+1`,
by the lower endpoint of its stored height interval.
Role: ensures positive heights and proves that the general height sequence diverges.
-/
theorem primitiveHorizontalHeightSeq_ge {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) :
    (k : ℝ) + 1 ≤ primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k :=
  (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).T_mem.1

/--
Under GRH, `2 ≤ N`, primitive nontrivial `χ`, and `χ⁻¹ ≠ 1`, the named height sequence
tends to infinity. Compare it pointwise with the diverging sequence `k+1`.
Role: supplies the heights used in the general-character horizontal contour limit.
-/
theorem tendsto_primitiveHorizontalHeightSeq_atTop {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv) Filter.atTop
      Filter.atTop := by
  have hnn_tendsto : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  exact
    Filter.tendsto_atTop_mono (primitiveHorizontalHeightSeq_ge hN2 hGRH hprimitive hne hinv)
      hnn_tendsto

/--
For the primitive-character GRH data and `|σ| ≤ 2`, the completed function is nonzero at
both `σ ± T_k i`. Project the chosen strip data's `nonzero` field.
Role: permits logarithmic-derivative identities on both horizontal contour edges.
-/
theorem primitiveHorizontalHeightSeq_completedLFunction_ne_zero {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {σ : ℝ} (hσ : |σ| ≤ 2) :
    DirichletCharacter.completedLFunction χ
          ((σ : ℂ) + primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) ≠
        0 ∧
      DirichletCharacter.completedLFunction χ
          ((σ : ℂ) - primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) ≠
        0 :=
  (primitiveHorizontalStripDataSeq hN2 hGRH hprimitive hne hinv k).nonzero σ hσ

/--
For the primitive-character GRH data and `|σ| ≤ 2`, the centered completed logarithmic
derivative at both `σ ± T_k i`, divided by `T_k²`, is bounded by the general strip envelope.
Proof: unfold the named height and apply the general epsilon bound.
Role: supplies the uniform bound whose envelope tends to zero in the horizontal contour limit.
-/
theorem primitiveHorizontalHeightSeq_completedLogDeriv_bound {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {σ : ℝ} (hσ : |σ| ≤ 2) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) +
                  primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k) ^ 2 ≤
        primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k ∧
      ‖logDeriv (DirichletCharacter.completedLFunction χ)
                ((σ : ℂ) -
                  primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (primitiveHorizontalHeightSeq hN2 hGRH hprimitive hne hinv k) ^ 2 ≤
        primitiveHorizontalStripEpsilon hN2 hGRH hprimitive hne hinv k :=
  primitiveHorizontalStripEpsilon_bound hN2 hGRH hprimitive hne hinv k hσ

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
