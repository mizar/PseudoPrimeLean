/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularArchimedeanBounds

/-! # Explicit primitive remainder for the alpha-18 triangular kernel

The left completed integral decays with scale and the gamma integral has a
uniform numerical bound. The actual contour formula yields both precise and
standard remainder contracts without supplied analytic error assumptions.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data and nonprincipal inverse, the normalized
alpha-18 completed left integral is at most 4*10^12*(norm(log q)+284)*x^(-9/16)
for positive x. Reflect the logarithmic derivative, keep the scale factor,
and apply the explicit fixed-line decay and logarithmic integral budgets.
This is the scale-decaying left contribution to the primitive contour remainder. -/
theorem triangular18_left_completedIntegral_norm_le_scaled {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      4000000000000 * (‖Complex.log q‖ + 284) * x ^ (-9 / 16 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let A := (‖Complex.log q‖ + 284) * x ^ (-9 / 16 : ℝ)
  have hA : 0 ≤ A :=
    mul_nonneg (add_nonneg (norm_nonneg _) (by norm_num only)) (Real.rpow_nonneg hx.le _)
  have hF (t : ℝ) : ‖F t‖ ≤ A * (Real.log (4 + |t|) + 1) := by
    have hr := triangular18_completed_left_reflection hp hne hinv t
    have hi :=
      AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_seventeen_sixteenths_le_log
        hinv (-t)
    simp only [Complex.ofReal_neg, mul_neg, abs_neg, ← sub_eq_add_neg] at hi
    have hb :=
      norm_add_le (Complex.log (q : ℂ))
        (logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t))
    have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
    have hg :
      ‖-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2)‖ ≤
        (‖Complex.log q‖ + 284) * (Real.log (4 + |t|) + 1) := by
      rw [hr]
      nlinarith only [hb, hi, hL, norm_nonneg (Complex.log (q : ℂ))]
    dsimp only [F, A]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hm := mul_le_mul_of_nonneg_right hg (Real.rpow_nonneg hx.le (-9 / 16))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  have hK (t : ℝ) :
    ‖K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤ 1000000000000 / (1 + t ^ 2) := by
    have hs : |(((-9 / 16 : ℝ) : ℂ) + Complex.I * t).re| = (9 / 16 : ℝ) := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only
    have hd := Analysis.triangular18_fixed_line_decay hs
    simpa only [K, triangularMellinKernel, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, one_mul, zero_mul, zero_add] using hd
  have hraw := norm_logWeighted_product_integral_le hA hF hK
  have hJ :=
    mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
      (mul_nonneg hA (by norm_num only : (0 : ℝ) ≤ 1000000000000))
  have hn := norm_mellinNormalization_mul_le_sixth (hraw.trans hJ)
  have he :
    (fun t : ℝ ↦
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (fun t : ℝ ↦ F t * K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    funext t
    dsimp only [F]
    ring
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * _‖ ≤ _
  rw [he]
  have hnum : (A * 1000000000000 * 22) / 6 ≤ 4000000000000 * A := by nlinarith only [hA]
  have h := hn.trans hnum
  simpa only [A, mul_assoc] using h

/-- For primitive nonprincipal GRH data of modulus at least two, nonprincipal
inverse and x>=1, the arithmetic sum plus oscillating zero sum has norm at most
4*10^12*(log(q)+284)*x^(-9/16)+55000. Apply the exact contour formula, remove
the zero pole, and add the explicit left and uniform gamma bounds.
This precise contract retains the scale decay for subsequent MR comparisons. -/
theorem triangular18_primitive_remainder_norm_le_precise {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤
      4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) + 55000 := by
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
  have hG : ‖G‖ ≤ 55000 :=
    triangular18_gammaIntegral_norm_le_uniform χ (by norm_num only : (0 : ℝ) ≤ 9 / 16)
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

/-- Nonnegative L, 0<=y<=1 and r<=y transfer the explicit left and gamma
budgets to 1.2*10^15*(1+L*y). Multiply the scale comparison by the nonnegative
coefficient and compare the resulting polynomial.
This is the rational budget conversion for the standard remainder form. -/
private theorem triangular18_remainder_budget {L y r : ℝ} (hL : 0 ≤ L) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    (hr : r ≤ y) : 4000000000000 * (L + 284) * r + 55000 ≤ 1200000000000000 * (1 + L * y) := by
  have hm :=
    mul_le_mul_of_nonneg_left hr
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4000000000000)
        (add_nonneg hL (by norm_num only : (0 : ℝ) ≤ 284)))
  have hLy := mul_nonneg hL hy
  nlinarith only [hm, hy1, hLy]

/-- For L>=0 and x>=1, the precise alpha-18 budget is at most
1.2*10^15*(1+L/sqrt(x)). Compare x^(-9/16) with 1/sqrt(x), whose value is
at most one, and apply the rational budget.
This converts the scale-decaying remainder to the standard primitive contract. -/
private theorem triangular18_coarse_remainder_budget {L x : ℝ} (hL : 0 ≤ L) (hx : 1 ≤ x) :
    4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) + 55000 ≤
      1200000000000000 * (1 + L / Real.sqrt x) := by
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hr := Real.rpow_le_rpow_of_exponent_le hx (by norm_num only : (-9 / 16 : ℝ) ≤ -(1 / 2))
  rw [Real.rpow_neg hxp.le, ← Real.sqrt_eq_rpow, ← one_div] at hr
  have hy : 0 ≤ 1 / Real.sqrt x := div_nonneg zero_le_one (Real.sqrt_nonneg x)
  have hy1 : 1 / Real.sqrt x ≤ 1 := by
    have h := one_div_le_one_div_of_le zero_lt_one (Real.one_le_sqrt.mpr hx)
    simpa only [div_one] using h
  have h := triangular18_remainder_budget hL hy hy1 hr
  simpa only [div_eq_mul_inv, one_mul] using h

/-- For primitive nonprincipal GRH data of modulus at least two, nonprincipal
inverse and x>=1, the actual alpha-18 arithmetic sum plus oscillating zero sum
has norm at most U18*(1+log(q)/sqrt(x)) with U18=1200000000000000.
Convert the proved precise contour remainder; no pole, integral, or kernel
budget remains as an extra premise. This is the standard primitive remainder API. -/
theorem triangular18_primitive_remainder_norm_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖(∑' n : ℕ, K.summand χ x n) + (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ)‖ ≤
      1200000000000000 * (1 + Real.log q / Real.sqrt x) := by
  have hb := triangular18_primitive_remainder_norm_le_precise hq hGRH hp hne hinv hx
  have hqR : (1 : ℝ) ≤ q := by
    simpa only [Nat.cast_one] using
      (Nat.cast_le.mpr ((by decide : 1 ≤ 2).trans hq) : ((1 : ℕ) : ℝ) ≤ (q : ℝ))
  exact hb.trans (triangular18_coarse_remainder_budget (Real.log_nonneg hqR) hx)

/-- For primitive nonprincipal GRH data of modulus at least two, nonprincipal
inverse and x>=1, the actual alpha-18 arithmetic sum is bounded by the explicit
finite-conductor zero mass plus the precise scale-decaying remainder.
Write the arithmetic sum as its zero-sum-corrected value minus the zero sum
and use the two proved norm estimates. This is the primitive input for averaging. -/
theorem triangular18_primitive_arithmetic_norm_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' n : ℕ, K.summand χ x n‖ ≤
      36 * Real.log q + 1350000000000000 +
        (4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) + 55000) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let S := ∑' n : ℕ, K.summand χ x n
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  have hR := triangular18_primitive_remainder_norm_le_precise hq hGRH hp hne hinv hx
  have hZ :=
    triangular18_oscillatingZeroSum_norm_le_explicit hq hGRH hp hne hinv (zero_lt_one.trans_le hx)
  change ‖S‖ ≤ _
  calc
    _ = ‖(S + Z) - Z‖ := congrArg norm (by ring)
    _ ≤ ‖S + Z‖ + ‖Z‖ := norm_sub_le _ _
    _ ≤
        (4000000000000 * (Real.log q + 284) * x ^ (-9 / 16 : ℝ) + 55000) +
          (36 * Real.log q + 1350000000000000) :=
      add_le_add hR hZ
    _ = _ := by ring

end PseudoPrime.LLS.PaperStatements
