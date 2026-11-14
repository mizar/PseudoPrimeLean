/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalExp
public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rational exponential approximations for the height-100 grid -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A nonpositive rational exponential with magnitude at most 11 is
approximated within `10⁻⁸` by the fixed rounded Taylor evaluator. -/
private theorem norm_real_exp_grid (v : ℚ) (hv0 : v ≤ 0) (hv : |(v : ℝ)| ≤ 11) :
    ‖Complex.exp (v : ℂ) -
          Analysis.rationalComplexCast (Analysis.rationalScaledRealExp (10 ^ 12) v 16 6)‖ ≤
      (1 / 100000000 : ℝ) := by
  have hred : |((v / (2 : ℚ) ^ 6 : ℚ) : ℝ)| ≤ 1 / 5 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 6 : ℚ) : ℝ)) hred 16
  have hsmall : ∀ j < 6, (Analysis.roundedSquareBudget (10 ^ 12) j : ℝ) ≤ 1 := by
    have hc : ∀ j : Fin 6, Analysis.roundedSquareBudget (10 ^ 12) j ≤ 1 := by decide +kernel
    intro j hj
    exact_mod_cast hc ⟨j, hj⟩
  have h :=
    Analysis.norm_scaled_real_exp_error (by norm_num only : 0 < 10 ^ 12) v hv0 16 6
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      hsmall
  norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at h
  linarith only [h]

/-- A rational phase of magnitude at most 700 is approximated within
`10⁻⁶` by the fixed rounded Taylor evaluator. -/
private theorem norm_phase_grid (v : ℚ) (hv : |(v : ℝ)| ≤ 700) :
    ‖Complex.exp (Complex.I * (v : ℂ)) -
          Analysis.rationalComplexCast (Analysis.rationalScaledPhase (10 ^ 12) v 16 11)‖ ≤
      (1 / 1000000 : ℝ) := by
  have hred : |((v / (2 : ℚ) ^ 11 : ℚ) : ℝ)| ≤ 7 / 20 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 11 : ℚ) : ℝ)) hred 16
  have hsmall : ∀ j < 11, (Analysis.roundedSquareBudget (10 ^ 12) j : ℝ) ≤ 1 := by
    have hc : ∀ j : Fin 11, Analysis.roundedSquareBudget (10 ^ 12) j ≤ 1 := by decide +kernel
    intro j hj
    exact_mod_cast hc ⟨j, hj⟩
  have h :=
    Analysis.norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 12) v 16 11
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      hsmall
  norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at h
  linarith only [h]

/-- The error in a product of approximations is bounded in terms of the
two input errors when the exact factors have norm at most one. -/
private theorem norm_product_approx (A B a b : ℂ) {e f : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
    (he : ‖A - a‖ ≤ e) (hf : ‖B - b‖ ≤ f) : ‖A * B - a * b‖ ≤ e + (1 + e) * f := by
  have ha : ‖a‖ ≤ 1 + e := by
    have h := norm_le_norm_sub_add a A
    rw [norm_sub_rev] at h
    linarith only [h, hA, he]
  have he0 : 0 ≤ e := le_trans (norm_nonneg _) he
  have hfirst : ‖A * B - a * B‖ ≤ e := by
    rw [← sub_mul, norm_mul]
    have h := mul_le_mul he hB (norm_nonneg B) he0
    nlinarith only [h]
  have hsecond : ‖a * B - a * b‖ ≤ (1 + e) * f := by
    rw [← mul_sub, norm_mul]
    exact mul_le_mul ha hf (norm_nonneg _) (by linarith only [he0])
  exact
    (norm_sub_le_norm_sub_add_norm_sub (A * B) (a * B) (a * b)).trans (add_le_add hfirst hsecond)

/-- Compute a rational complex approximation for `exp(-(σ + 100i)q)` at
`σ = 1/2 + k/128`. The two components are produced by independently rounded
real-exponential and phase evaluators, then multiplied as rational pairs. -/
def gridPowerApprox (k : ℕ) (q : ℚ) : ℚ × ℚ :=
  Analysis.rationalComplexMul
    (Analysis.rationalScaledRealExp (10 ^ 12) (-(1 / 2 + (k : ℚ) / 128) * q) 16 6)
    (Analysis.rationalScaledPhase (10 ^ 12) (-(100 : ℚ) * q) 16 11)

/-- If `0 ≤ k ≤ 128` and `0 ≤ q ≤ 7`, the rational grid evaluator
approximates `exp(-(1/2 + k/128 + 100i)q)` within `10⁻⁵`. The proof
combines separate certified exponential and phase errors. -/
theorem norm_grid_power_approx (k : ℕ) (hk : k ≤ 128) (q : ℚ) (hq0 : 0 ≤ q) (hq7 : q ≤ 7) :
    ‖Complex.exp (-((((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I)) * (q : ℂ)) -
          Analysis.rationalComplexCast (gridPowerApprox k q)‖ ≤
      (1 / 100000 : ℝ) := by
  let v : ℚ := -(1 / 2 + (k : ℚ) / 128) * q
  let w : ℚ := -(100 : ℚ) * q
  have hk0 : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hk128 : (k : ℚ) ≤ 128 := by exact_mod_cast hk
  have hσ0 : (0 : ℚ) ≤ 1 / 2 + (k : ℚ) / 128 := by nlinarith only [hk0]
  have hσ : (1 / 2 + (k : ℚ) / 128) ≤ 3 / 2 := by nlinarith only [hk128]
  have hv0 : v ≤ 0 := by
    dsimp only [v]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ0) hq0
  have hqprod := mul_le_mul hσ hq7 hq0 (by norm_num only : (0 : ℚ) ≤ 3 / 2)
  have hvlo : -(11 : ℚ) ≤ v := by
    dsimp only [v]; nlinarith only [hqprod]
  have hw0 : w ≤ 0 := by
    dsimp only [w]; nlinarith only [hq0]
  have hwlo : -(700 : ℚ) ≤ w := by
    dsimp only [w]; nlinarith only [hq7]
  have hvR0 : (v : ℝ) ≤ 0 := by exact_mod_cast hv0
  have hvRlo : -(11 : ℝ) ≤ v := by exact_mod_cast hvlo
  have hwR0 : (w : ℝ) ≤ 0 := by exact_mod_cast hw0
  have hwRlo : -(700 : ℝ) ≤ w := by exact_mod_cast hwlo
  have hv : |(v : ℝ)| ≤ 11 := abs_le.mpr ⟨hvRlo, by linarith only [hvR0]⟩
  have hw : |(w : ℝ)| ≤ 700 := abs_le.mpr ⟨hwRlo, by linarith only [hwR0]⟩
  have ha : ‖Complex.exp (v : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_exp, ← Complex.ofReal_ratCast, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr hvR0
  have hb : ‖Complex.exp (Complex.I * (w : ℂ))‖ ≤ 1 := by
    rw [← Complex.ofReal_ratCast, Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im]
    norm_num only [zero_mul, sub_zero, Real.exp_zero, le_refl]
  have he := norm_real_exp_grid v hv0 hv
  have hf := norm_phase_grid w hw
  have hp := norm_product_approx _ _ _ _ ha hb he hf
  have heq :
    (-((((1 / 2 + (k : ℝ) / 128 : ℝ) : ℂ) + ((100 : ℝ) : ℂ) * Complex.I))) * (q : ℂ) =
      (v : ℂ) + Complex.I * (w : ℂ) := by
    dsimp only [v, w]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_natCast, Rat.cast_one, Complex.ofReal_add, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [heq, Complex.exp_add]
  change
    ‖Complex.exp (v : ℂ) * Complex.exp (Complex.I * (w : ℂ)) -
          Analysis.rationalComplexCast
            (Analysis.rationalComplexMul (Analysis.rationalScaledRealExp (10 ^ 12) v 16 6)
              (Analysis.rationalScaledPhase (10 ^ 12) w 16 11))‖ ≤
      _
  rw [Analysis.rationalComplexCast_mul]
  linarith only [hp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
