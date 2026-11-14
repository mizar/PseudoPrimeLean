/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerArithmetic

/-! # Error bounds for the low-zero rational power evaluator -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The fixed rounded phase evaluator approximates `exp(iv)` within `10⁻⁹`
for `|v| ≤ 700`. Its Taylor remainder and all eleven rounding budgets are
bounded by exact rational calculations. -/
theorem norm_endpoint_phase (v : ℚ) (hv : |(v : ℝ)| ≤ 700) :
    ‖Complex.exp (Complex.I * (v : ℂ)) -
          Analysis.rationalComplexCast (Analysis.rationalScaledPhase (10 ^ 15) v 16 11)‖ ≤
      (1 / 1000000000 : ℝ) := by
  have hred : |((v / (2 : ℚ) ^ 11 : ℚ) : ℝ)| ≤ 7 / 20 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 11 : ℚ) : ℝ)) hred 16
  have hsmall : ∀ j < 11, (Analysis.roundedSquareBudget (10 ^ 15) j : ℝ) ≤ 1 := by
    have hc : ∀ j : Fin 11, Analysis.roundedSquareBudget (10 ^ 15) j ≤ 1 := by decide +kernel
    intro j hj
    exact_mod_cast hc ⟨j, hj⟩
  have h :=
    Analysis.norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 15) v 16 11
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      hsmall
  norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at h
  linarith only [h]

/-- The fixed rounded real exponential evaluator has error at most `10⁻¹¹`
for nonpositive rational inputs with absolute value at most 11. -/
private theorem norm_endpoint_real_exp (v : ℚ) (hv0 : v ≤ 0) (hv : |(v : ℝ)| ≤ 11) :
    ‖Complex.exp (v : ℂ) -
          Analysis.rationalComplexCast (Analysis.rationalScaledRealExp (10 ^ 15) v 16 6)‖ ≤
      (1 / 100000000000 : ℝ) := by
  have hred : |((v / (2 : ℚ) ^ 6 : ℚ) : ℝ)| ≤ 1 / 5 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 6 : ℚ) : ℝ)) hred 16
  have hsmall : ∀ j < 6, (Analysis.roundedSquareBudget (10 ^ 15) j : ℝ) ≤ 1 := by
    have hc : ∀ j : Fin 6, Analysis.roundedSquareBudget (10 ^ 15) j ≤ 1 := by decide +kernel
    intro j hj
    exact_mod_cast hc ⟨j, hj⟩
  have h :=
    Analysis.norm_scaled_real_exp_error (by norm_num only : 0 < 10 ^ 15) v hv0 16 6
      (by
        norm_num only; linarith only [hred])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      hsmall
  norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at h
  linarith only [h]

/-- If two exact factors have norm at most one, the product error is bounded
by the first error plus the second error times the approximate first norm. -/
private theorem norm_endpoint_product (A B a b : ℂ) {e f : ℝ} (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1)
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

/-- For rational `0 ≤ t ≤ 100` and `0 ≤ q ≤ 7`, the rounded evaluator
approximates `exp(-(1/2 + it)q)` within `1/500000000`. Its two factors
are certified independently and then combined by the product estimate. -/
theorem norm_endpoint_power_approx (t q : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100) (hq0 : 0 ≤ q)
    (hq : q ≤ 7) :
    ‖Complex.exp (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I)) * (q : ℂ)) -
          Analysis.rationalComplexCast (endpointPowerApprox t q)‖ ≤
      (1 / 500000000 : ℝ) := by
  let v : ℚ := -(1 / 2 : ℚ) * q
  let w : ℚ := -t * q
  have hv0 : v ≤ 0 := by
    dsimp only [v]; nlinarith only [hq0]
  have hvlo : -(11 : ℚ) ≤ v := by
    dsimp only [v]; nlinarith only [hq]
  have hprod := mul_le_mul ht hq hq0 (by norm_num only : (0 : ℚ) ≤ 100)
  have hw0 : w ≤ 0 := by
    dsimp only [w]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht0) hq0
  have hwlo : -(700 : ℚ) ≤ w := by
    dsimp only [w]; nlinarith only [hprod]
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
  have he := norm_endpoint_real_exp v hv0 hv
  have hf := norm_endpoint_phase w hw
  have hp := norm_endpoint_product _ _ _ _ ha hb he hf
  have heq :
    (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))) * (q : ℂ) =
      (v : ℂ) + Complex.I * (w : ℂ) := by
    dsimp only [v, w]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one,
      Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    rw [Complex.ofReal_ratCast]
    ring
  rw [heq, Complex.exp_add]
  change
    ‖Complex.exp (v : ℂ) * Complex.exp (Complex.I * (w : ℂ)) -
          Analysis.rationalComplexCast
            (Analysis.rationalComplexMul (Analysis.rationalScaledRealExp (10 ^ 15) v 16 6)
              (Analysis.rationalScaledPhase (10 ^ 15) w 16 11))‖ ≤
      _
  rw [Analysis.rationalComplexCast_mul]
  linarith only [hp]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
