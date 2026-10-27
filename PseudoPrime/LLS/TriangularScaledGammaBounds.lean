/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.Analysis.TriangularDigammaMoments
public import PseudoPrime.LLS.TriangularPrimitiveRemainderBounds

/-! # Gamma integral bounds using the natural triangular height scale -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At every real height, the alpha-18 imaginary kernel is at most
2592 divided by one plus the square of eighteen times the height.
Combine the uniform sinc bound and the height-square moment bound.
This retains the natural narrow width in the Gamma integral majorant. -/
theorem triangular18_central_decay_scaled (t : ℝ) :
    ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖ ≤ 2592 / (1 + (18 * t) ^ 2) := by
  have hn : ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖ ≤ (1296 : ℝ) := by
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (18 : ℝ) ≠ 0)]
    have hs := Real.abs_sinc_le_one (18 * t)
    have ha := sq_abs (Real.sinc (18 * t))
    nlinarith only [hs, ha, abs_nonneg (Real.sinc (18 * t))]
  have ht :=
    Analysis.triangularMellinFunction_height_sq_norm_le_four (by norm_num only : (18 : ℝ) ≠ 0) t
  apply (le_div_iff₀ (by linarith only [sq_nonneg (18 * t)] : (0 : ℝ) < 1 + (18 * t) ^ 2)).mpr
  nlinarith only [hn, ht]

/-- For every character and positive scale, the raw central Gamma integral norm
is at most 34848. Bound its phase by one, use the rescaled kernel decay,
and change height by a factor eighteen in the logarithmic integral.
This improves the previous bound obtained with an unscaled decay envelope. -/
theorem triangular18_central_gammaIntegral_norm_le_scaled_decay {q : ℕ} (χ : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction 18 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      34848 := by
  let f := fun t : ℝ ↦ (Real.log (4 + |t|) + 1) / (1 + t ^ 2)
  have hf :=
    (MeasureTheory.integrable_comp_mul_left_iff f (by norm_num only : (18 : ℝ) ≠ 0)).mpr
      Analysis.integrable_log_add_abs_div_one_add_sq
  have hi :=
    MeasureTheory.norm_integral_le_of_norm_le (f := fun t : ℝ ↦
      logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
        (Analysis.triangularMellinFunction 18 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)))
      (hf.const_mul (11 * 2592 : ℝ))
      (MeasureTheory.ae_of_all _
        (fun t : ℝ ↦ by
          have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
            simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
              Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
              Complex.div_ofNat_re, Complex.one_re, zero_add]
          have hg := triangular_gamma_central_log_bound χ hr
          have hlog :=
            Real.log_le_log (by linarith only [abs_nonneg t] : (0 : ℝ) < 4 + |t|)
              (by
                rw [abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 18)]
                nlinarith only [abs_nonneg t] : 4 + |t| ≤ 4 + |18 * t|)
          have hp : 0 ≤ Real.log (4 + |18 * t|) :=
            Real.log_nonneg (by linarith only [abs_nonneg (18 * t)])
          simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
            zero_div, add_zero] at hg
          have hb :
            ‖logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)‖ ≤
              11 * (Real.log (4 + |18 * t|) + 1) := by
            linarith only [hg, hlog, hp]
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
          simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
          have h :=
            mul_le_mul hb (triangular18_central_decay_scaled t) (norm_nonneg _)
              (by linarith only [hp] : 0 ≤ 11 * (Real.log (4 + |18 * t|) + 1))
          exact
            h.trans_eq
              (by
                dsimp only [f]; ring)))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.Measure.integral_comp_mul_left] at hi
  norm_num only [abs_of_pos (by norm_num only : (0 : ℝ) < (18 : ℝ)⁻¹), smul_eq_mul] at hi
  have hb := Analysis.logarithmic_inverseSquare_integral_le_twenty_two
  dsimp only [f] at hi
  linarith only [hi, hb]

/-- For every character, scale at least one, and line between zero and five eighths,
the normalized Gamma integral norm is at most 6000.
Shift to the central line and normalize the rescaled raw bound 34848.
This reduces the uniform Gamma cost in the primitive contour remainder. -/
theorem triangular18_gammaIntegral_norm_le_six_thousand {q : ℕ} (χ : DirichletCharacter ℂ q)
    {b x : ℝ} (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      (6000 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have he :=
    MellinKernel.gammaIntegral_eq_central K χ hb
      (by
        change b ≤ 1 / 2 + 1 / 8; linarith only [hbK])
      (by linarith only [hbK]) hx
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * _‖ ≤ _
  rw [he]
  have hraw := triangular18_central_gammaIntegral_norm_le_scaled_decay χ (zero_lt_one.trans_le hx)
  have hn := norm_mellinNormalization_mul_le_sixth hraw
  exact hn.trans (by norm_num only : (34848 : ℝ) / 6 ≤ 6000)

/-- For primitive nonprincipal GRH data with nonprincipal inverse, modulus at least two,
and scale at least one, the arithmetic plus oscillating zero sum has norm at most
4 times ten to the twelfth times (log q plus 284) times the scale to minus nine sixteenths,
plus 6000. Apply the exact contour formula and the improved uniform Gamma bound.
This retains the existing left-contour decay while reducing the Gamma cost. -/
theorem triangular18_primitive_remainder_norm_le_scaled_gamma {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤
      4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) + 6000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let R :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  let G :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hR : ‖R‖ ≤ 4000000000000 * (‖Complex.log q‖ + 284) * x ^ (-9 / 16 : ℝ) :=
    triangular18_left_completedIntegral_norm_le_scaled hp hne hinv (zero_lt_one.trans_le hx)
  have hqR : (1 : ℝ) ≤ q := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr ((by decide : 1 ≤ 2).trans hq) : ((1 : ℕ) : ℝ) ≤ (q : ℝ))
  rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hqR)] at hR
  have hG : ‖G‖ ≤ 6000 :=
    triangular18_gammaIntegral_norm_le_six_thousand χ (by norm_num only : (0 : ℝ) ≤ 9 / 16)
      (by norm_num only : (9 / 16 : ℝ) ≤ 5 / 8) hx
  have he :=
    MellinKernel.tsum_summand_eq_completed_residue_formula K hq hGRH hp hne hinv (a := -9 / 16)
      (b := 9 / 16) (x := x) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  dsimp only at he
  rw [triangular_weightedResidue_pole_eq_zero, zero_sub] at he
  have he' : (∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) = R + G := by
    linear_combination he
  change ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤ _
  rw [he']
  exact (norm_add_le R G).trans (add_le_add hR hG)

end PseudoPrime.LLS.PaperStatements
