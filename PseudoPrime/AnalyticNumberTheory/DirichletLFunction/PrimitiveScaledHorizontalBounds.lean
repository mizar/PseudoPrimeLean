/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveHorizontalLogDerivBound

/-!
# Vanishing envelopes on growing horizontal strips

Scaled good-height data separate the character-specific existence theorem from the
real estimates. Their normalized centered derivative envelope tends to zero for any
admissible family. Individual character RH supplies such a family.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Height, radius and separation data for a character at real scale `n`.
The fields require `T ∈ [n,2n]`, `R ∈ [8n,16n]`, a positive explicit margin `δ`, and
centered logarithmic-derivative bounds and nonvanishing at both heights `±T` throughout
`|σ| ≤ 2n`. These conditions are part of the data; existence for a primitive nonprincipal
character is proved using individual RH. Growing scales cover every fixed horizontal strip. -/
structure PrimitiveScaledHorizontalStripData {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (n : ℝ) where
  /-- The ordinate used for both horizontal edges; `T_mem` makes it positive when n >= 1. -/
  T : ℝ
  /-- The radius controlling the finite Hadamard error terms. -/
  R : ℝ
  /-- The positive separation margin in the logarithmic-derivative bound. -/
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
                δ
  /-- Nonvanishing at both signs of the height, uniformly for `|σ| ≤ 2 * n`.
  The completed-to-ordinary logarithmic-derivative bridge uses this alongside `bound`. -/
  nonzero :
    ∀ σ : ℝ,
      |σ| ≤ 2 * n →
        DirichletCharacter.completedLFunction χ ((σ : ℂ) + T * Complex.I) ≠ 0 ∧
          DirichletCharacter.completedLFunction χ ((σ : ℂ) - T * Complex.I) ≠ 0

/-- For any supplied family of scaled horizontal data at n = k+1, divide its three
centered logarithmic-derivative error terms, with the point norm replaced by 4n,
by the selected height squared. The real envelope uses the family's radius and margin.
For a primitive nonprincipal character with nonprincipal inverse and level at least two,
it bounds both signed horizontal derivatives and tends to zero. -/
noncomputable def scaledHorizontalStripEpsilon {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1)) (k : ℕ) : ℝ :=
  let n : ℝ := (k : ℝ) + 1
  let d := data k
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

/-- For primitive non-principal `χ` and its non-principal inverse, the normalized envelope
bounds the centered completed logarithmic derivative at both selected heights throughout
the growing strip. The proof uses the supplied bound and the height and radius ranges. -/
theorem scaledHorizontalStripEpsilon_bound {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1))
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) {σ : ℝ}
    (hσ : |σ| ≤ 2 * ((k : ℝ) + 1)) :
    ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) + (data k).T * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (data k).T ^ 2 ≤
        scaledHorizontalStripEpsilon data k ∧
      ‖logDeriv (DirichletCharacter.completedLFunction χ) ((σ : ℂ) - (data k).T * Complex.I) -
              logDeriv (DirichletCharacter.completedLFunction χ) 0‖ /
          (data k).T ^ 2 ≤
        scaledHorizontalStripEpsilon data k := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  set n : ℝ := (k : ℝ) + 1 with hn_def
  set d := data k with hd_def
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
      _ ≤ scaledHorizontalStripEpsilon data k := by
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
      _ ≤ scaledHorizontalStripEpsilon data k := by
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

/-- Any admissible scaled family for a primitive non-principal character is eventually
bounded by a clean envelope with a positive constant. Radius growth and the explicit
separation margin reduce the three terms to powers and logarithms of the scale. -/
theorem eventually_scaledHorizontalStripEpsilon_le_cleanEnvelope {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1))
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    ∃ K : ℝ,
      0 < K ∧
        ∀ᶠ k : ℕ in Filter.atTop,
          scaledHorizontalStripEpsilon data k ≤
            primitiveHorizontalStripCleanEnvelope (χ := χ) K ((k : ℝ) + 1) := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  obtain ⟨K, hKpos, hKevent⟩ := exists_K_forall_H2LogBound_thirtyTwo_le hN2 hprimitive hne
  refine ⟨K, hKpos, ?_⟩
  have hnn_tendsto : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have hKevent_k := hnn_tendsto.eventually hKevent
  filter_upwards [hKevent_k] with k hk
  set n : ℝ := (k : ℝ) + 1 with hn_def
  set d := data k with hd_def
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

/-- The scaled envelope is nonnegative for a primitive non-principal character and its
non-principal inverse. Positivity of the radius, margin and zero-count terms proves the
claim, supplying the lower bound needed for the subsequent squeeze argument. -/
theorem scaledHorizontalStripEpsilon_nonneg {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1))
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) :
    0 ≤ scaledHorizontalStripEpsilon data k := by
  have hN1 : 1 < N := Nat.lt_of_lt_of_le (by norm_num only) hN2
  set d := data k with hd_def
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

/-- For any admissible scaled family, its normalized centered derivative envelope tends
to zero. The eventual clean-envelope estimate and nonnegativity permit a squeeze argument;
this conclusion requires no further hypothesis about how the family was chosen. -/
theorem tendsto_scaledHorizontalStripEpsilon_atTop {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (data : ∀ k : ℕ, PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1))
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    Filter.Tendsto (scaledHorizontalStripEpsilon data) Filter.atTop (nhds 0) := by
  obtain ⟨K, hKpos, hKle⟩ :=
    eventually_scaledHorizontalStripEpsilon_le_cleanEnvelope hN2 data hprimitive hne hinv
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
        (scaledHorizontalStripEpsilon_nonneg hN2 data hprimitive hne hinv))
      hKle

/-- Choose growing-strip good-height data for primitive non-principal `χ` under its own
Riemann hypothesis, with scale at least one and non-principal inverse. The existence theorem
provides all ranges, separation, derivative bounds and nonvanishing fields. -/
noncomputable def primitiveScaledHorizontalStripData_of_dirichletRH {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {n : ℝ} (hn : 1 ≤ n) :
    PrimitiveScaledHorizontalStripData χ n := by
  choose T hT R hR δ hδpos hδeq hall using
    exists_primitiveHorizontalScaledStripLogDerivBound_of_dirichletRH hN2 hRH hp hne hinv hn
  exact
    ⟨T, R, δ, hT, hR, hδpos, hδeq, fun σ hσ ↦ ⟨(hall σ hσ).1, (hall σ hσ).2.1⟩, fun σ hσ ↦
      (hall σ hσ).2.2⟩

/-- Choose good-height data at scale `k + 1` under the individual character's Riemann
hypothesis. The heights grow at least linearly, and the strips exhaust every fixed strip;
the generic envelope theorem applies to this sequence. -/
noncomputable def primitiveScaledHorizontalStripDataSeq_of_dirichletRH {N : ℕ} [NeZero N]
    (hN2 : 2 ≤ N) {χ : DirichletCharacter ℂ N} (hRH : GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (k : ℕ) :
    PrimitiveScaledHorizontalStripData χ ((k : ℝ) + 1) :=
  primitiveScaledHorizontalStripData_of_dirichletRH hN2 hRH hp hne hinv
    (by linarith only [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))])

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
