/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.AnalyticConductor

/-!
# Fixed-parameter conductor and reference-line growth

The logarithmic conductor bound supplies an affine height bound. This coarser
consequence suffices when compactly supported smooth test transforms decrease
faster than every power; it does not replace uniform logarithmic estimates.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For positive natural conductor q, the logarithmic analytic conductor
is bounded by log q plus degree times the logarithm of norm(s)+3 plus the
sum of parameter norms. The triangle inequality dominates every positive
factor. This gives height bounds for a fixed parameter vector. -/
theorem log_analyticConductor_le_shiftNormSum {d : ℕ} (q : ℕ) (hq : 1 ≤ q) (κ : Fin d → ℂ) (s : ℂ) :
    Real.log (analyticConductor q κ s) ≤
      Real.log q + (d : ℝ) * Real.log (‖s‖ + 3 + ∑ j : Fin d, ‖κ j‖) := by
  have hb : ∀ j : Fin d, Real.log (‖s + κ j‖ + 3) ≤ Real.log (‖s‖ + 3 + ∑ k : Fin d, ‖κ k‖) := by
    intro j
    have hn := norm_add_le s (κ j)
    have hk := Finset.single_le_sum (fun k _ ↦ norm_nonneg (κ k)) (Finset.mem_univ j)
    have hp : 0 < ‖s + κ j‖ + 3 := by linarith only [norm_nonneg (s + κ j)]
    exact Real.log_le_log hp (by linarith only [hn, hk])
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hb j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  rw [log_analyticConductor q hq κ]
  linarith only [hh]

/-- For a fixed parameter vector, replace the logarithmic height profile
in the analytic conductor bound by its positive argument. The elementary
logarithm inequality gives an affine norm bound sufficient for contour
limits with rapidly decreasing compact-support test transforms. -/
theorem log_analyticConductor_le_linear {d : ℕ} (q : ℕ) (hq : 1 ≤ q) (κ : Fin d → ℂ) (s : ℂ) :
    Real.log (analyticConductor q κ s) ≤ Real.log q + (d : ℝ) * (‖s‖ + 3 + ∑ j : Fin d, ‖κ j‖) := by
  have hp : 0 < ‖s‖ + 3 + ∑ j : Fin d, ‖κ j‖ := by
    have hh : 0 ≤ ∑ j : Fin d, ‖κ j‖ := Finset.sum_nonneg (fun j _ ↦ norm_nonneg (κ j))
    linarith only [hh, norm_nonneg s]
  have hb := Real.log_le_sub_one_of_pos hp
  have hl : Real.log (‖s‖ + 3 + ∑ j : Fin d, ‖κ j‖) ≤ ‖s‖ + 3 + ∑ j : Fin d, ‖κ j‖ := by
    linarith only [hb]
  exact
    (log_analyticConductor_le_shiftNormSum q hq κ s).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg d)))

/-- The norm of 3+iT is at most 3+abs(T). Apply the triangle inequality and
the real and imaginary unit norms. This converts the conductor norm bound
into a height bound at the reference line. -/
theorem norm_three_add_imaginary_le (T : ℝ) : ‖(((3 : ℝ) : ℂ) + T * Complex.I)‖ ≤ 3 + |T| := by
  simpa only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)] using
    norm_add_le (((3 : ℝ) : ℂ)) ((T : ℂ) * Complex.I)

/-- For a regularized completion with the general complex gamma parameter
range and the arithmetic logarithmic derivative series, its logarithmic
derivative at 3+iT has an explicit affine height bound. Combine the conductor
logarithm norm estimate, the affine conductor bound, and norm(3+iT)<=3+abs(T).
This is a fixed-data growth bound for explicit-formula contour limits. -/
theorem norm_logDeriv_at_three_le_affine_height {F L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n) (T : ℝ)
    (hL : L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ ≤
      2 * |(k : ℝ)| + Real.log q / 2 +
        (d : ℝ) *
          ((|T| + 6 + ∑ j : Fin d, ‖κ j‖) / 2 +
            (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
            ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) := by
  have hs3 : ((((3 : ℝ) : ℂ) + T * Complex.I)).re = 3 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hb := norm_logDeriv_le_log_analyticConductor_at_three hq k κ hκ hreg ha hs3 hL hdL hlog
  have hc := log_analyticConductor_le_linear q hq κ (((3 : ℝ) : ℂ) + T * Complex.I)
  have hn := norm_three_add_imaginary_le T
  have hh := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg d : (0 : ℝ) ≤ _)
  linarith only [hb, hc, hh]

/-- Given the completion identity and a valid arithmetic logarithmic
derivative series all along the reference line, a positive constant bounds
the completed logarithmic derivative by A times (1+abs(T)) at every height.
Absorb the explicit affine intercept and degree into A. This removes a
separate reference-line growth assumption from good-height contour bounds. -/
theorem exists_norm_logDeriv_at_three_le_linear_height {F L : ℂ → ℂ} {q d : ℕ} (hq : 1 ≤ q) (k : ℤ)
    (κ : Fin d → ℂ) (hκ : ∀ j, -1 < (κ j).re)
    (hreg :
      ∀ z,
        z ≠ 0 →
          z ≠ 1 → F z = (z * (1 - z)) ^ k * ((q : ℂ) ^ (z / 2) * archimedeanGammaFactor κ z * L z))
    {a : ℕ → ℂ} (ha : ∀ n, ‖a n‖ ≤ (d : ℝ) * n * Real.log n)
    (hL : ∀ T : ℝ, L (((3 : ℝ) : ℂ) + T * Complex.I) ≠ 0)
    (hdL : ∀ T : ℝ, DifferentiableAt ℂ L (((3 : ℝ) : ℂ) + T * Complex.I))
    (hlog :
      ∀ T : ℝ,
        logDeriv L (((3 : ℝ) : ℂ) + T * Complex.I) = -LSeries a (((3 : ℝ) : ℂ) + T * Complex.I)) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, ‖logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)‖ ≤ A * (1 + |T|) := by
  let B : ℝ :=
    2 * |(k : ℝ)| + Real.log q / 2 +
      (d : ℝ) *
        ((6 + ∑ j : Fin d, ‖κ j‖) / 2 +
          (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
          ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2)
  refine ⟨1 + |B| + (d : ℝ), ?_, ?_⟩
  · linarith only [abs_nonneg B, (Nat.cast_nonneg d : (0 : ℝ) ≤ (d : ℝ))]
  · intro T
    have hb := norm_logDeriv_at_three_le_affine_height hq k κ hκ hreg ha T (hL T) (hdL T) (hlog T)
    have he :
      2 * |(k : ℝ)| + Real.log q / 2 +
          (d : ℝ) *
            ((|T| + 6 + ∑ j : Fin d, ‖κ j‖) / 2 +
              (‖Complex.log (Real.pi : ℂ)‖ + Real.pi + Gamma.digammaLogErrorBound) / 2 +
              ∑' n : ℕ, Real.log n / (n : ℝ) ^ 2) =
        B + (d : ℝ) / 2 * |T| := by
      dsimp only [B]; ring
    rw [he] at hb
    nlinarith only [hb, le_abs_self B, abs_nonneg T, abs_nonneg B,
      mul_nonneg (abs_nonneg B) (abs_nonneg T),
      mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ _) (abs_nonneg T)]

end PseudoPrime.AnalyticNumberTheory.General
