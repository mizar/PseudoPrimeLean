/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaNegativeInversion
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds

/-! # Euler-series cancellation after negative-strip Gamma inversion -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative u, the subtracted exponential has absolute value at most u.
The tangent at zero and exp(-u) at most one give both signs. This supplies the
extra inverse-scale factor after negative-strip Gamma inversion. -/
theorem abs_exp_neg_sub_one_le {u : ℝ} (hu : 0 ≤ u) : |Real.exp (-u) - 1| ≤ u := by
  have hl := Real.add_one_le_exp (-u)
  have hh := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  rw [abs_of_nonpos (sub_nonpos.mpr hh)]
  linarith only [hl]

/-- For a Gamma line strictly between minus one and zero and positive u, the actual
inverse Mellin transform has norm at most u. Apply the exact subtracted Gamma
inversion before taking norms. This retains the origin-residue cancellation. -/
theorem norm_mellinInv_Gamma_negative_le {c u : ℝ} (hlo : -1 < c) (hhi : c < 0) (hu : 0 < u) :
    ‖mellinInv c Complex.Gamma u‖ ≤ u := by
  rw [mellinInv_Gamma_negative hlo hhi hu, Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_neg_sub_one_le hu.le

/-- The real Euler kernel after Gamma inversion at reciprocal base nx.
The division by n sqrt x incorporates the reflected Dirichlet coefficient and half shift.
At n=0 the kernel is zero. It is dominated by 1/(x sqrt x n^2) at positive scale. -/
noncomputable def reflectedEulerKernel (x : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (-((n : ℝ) * x)⁻¹) - 1) / ((n : ℝ) * Real.sqrt x)

/-- For positive x and any natural n, the reflected kernel is bounded by
1/(x sqrt x n^2). Treat n=0 separately, then use the exponential tangent.
This turns the reflected Euler series into a convergent square-power majorant. -/
theorem abs_reflectedEulerKernel_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    |reflectedEulerKernel x n| ≤ (1 / (x * Real.sqrt x)) / (n : ℝ) ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp only [reflectedEulerKernel, Nat.cast_zero, zero_mul, div_zero, abs_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_refl]
  · have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hs := Real.sqrt_pos.mpr hx
    have hu := abs_exp_neg_sub_one_le (inv_nonneg.mpr (mul_nonneg hn0.le hx.le))
    have hd : 0 < (n : ℝ) * Real.sqrt x := mul_pos hn0 hs
    rw [reflectedEulerKernel, abs_div, abs_of_pos hd]
    have he :
      ((n : ℝ) * x)⁻¹ / ((n : ℝ) * Real.sqrt x) = (1 / (x * Real.sqrt x)) / (n : ℝ) ^ 2 := by
      field_simp [hn0.ne', hx.ne', hs.ne']
    exact (div_le_div_of_nonneg_right hu hd.le).trans_eq he

/-- For positive x and complex coefficients bounded by Mangoldt weights, each
inverted Euler term is dominated by the square-power Mangoldt majorant.
Multiply the kernel estimate by the coefficient norm. This supports absolute convergence. -/
theorem norm_reflectedEulerTerm_le {x : ℝ} (hx : 0 < x) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) (n : ℕ) :
    ‖a n * (reflectedEulerKernel x n : ℂ)‖ ≤
      (1 / (x * Real.sqrt x)) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have he :=
    mul_le_mul (ha n) (abs_reflectedEulerKernel_le hx n) (abs_nonneg _)
      ArithmeticFunction.vonMangoldt_nonneg
  exact he.trans_eq (by ring)

/-- For positive x and coefficients bounded by Mangoldt weights, the actual
inverted Euler series is summable. Dominate norms by the convergent Mangoldt
series at exponent two. This justifies the subsequent infinite norm bound. -/
theorem summable_reflectedEulerTerms {x : ℝ} (hx : 0 < x) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) :
    Summable (fun n ↦ a n * (reflectedEulerKernel x n : ℂ)) := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.summable_vonMangoldt_div_rpow (by norm_num only : (1 : ℝ) < 2)
  simp only [Real.rpow_two] at hs
  exact
    (hs.mul_left (1 / (x * Real.sqrt x))).of_norm_bounded
      (fun n ↦ norm_reflectedEulerTerm_le hx a ha n)

/-- For positive x and Mangoldt-dominated coefficients, the inverted Euler sum
has norm at most the exponent-two Mangoldt series divided by x sqrt x.
Use absolute convergence before comparing infinite sums. This retains the scale saving. -/
theorem norm_tsum_reflectedEulerTerms_le {x : ℝ} (hx : 0 < x) (a : ℕ → ℂ)
    (ha : ∀ n, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n) :
    ‖∑' n, a n * (reflectedEulerKernel x n : ℂ)‖ ≤
      (1 / (x * Real.sqrt x)) * ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ 2 := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.summable_vonMangoldt_div_rpow (by norm_num only : (1 : ℝ) < 2)
  simp only [Real.rpow_two] at hs
  have hn := norm_tsum_le_tsum_norm (summable_reflectedEulerTerms hx a ha).norm
  have hb :=
    Summable.tsum_le_tsum (fun n ↦ norm_reflectedEulerTerm_le hx a ha n)
      (summable_reflectedEulerTerms hx a ha).norm (hs.mul_left (1 / (x * Real.sqrt x)))
  rw [tsum_mul_left] at hb
  exact hn.trans hb

/-- For positive x and natural n and a negative Gamma line between minus one and zero,
the reflected kernel equals its actual inverse Mellin expression with factor 1/(n sqrt x).
Apply exact negative-strip inversion. This connects the real kernel to Mellin consumers. -/
theorem reflectedEulerKernel_eq_mellinInv {c x : ℝ} (hlo : -1 < c) (hhi : c < 0) (hx : 0 < x)
    {n : ℕ} (hn : 0 < n) :
    (reflectedEulerKernel x n : ℂ) =
      ((1 / ((n : ℝ) * Real.sqrt x) : ℝ) : ℂ) * mellinInv c Complex.Gamma (((n : ℝ) * x)⁻¹) := by
  rw [mellinInv_Gamma_negative hlo hhi (inv_pos.mpr (mul_pos (Nat.cast_pos.mpr hn) hx))]
  rw [← Complex.ofReal_mul]
  congr 1
  dsimp only [reflectedEulerKernel]
  ring

/-- For any complex Dirichlet character and positive scale, the inverted Euler
series has norm at most 1/(x sqrt x), without GRH or primitivity. Character norms
are at most one, and the certified Euler-ratio bound at exponent two is at most one.
This supplies a conductor-free candidate for the ordinary Euler part of the left contour. -/
theorem norm_twisted_reflectedEuler_tsum_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖∑' n : ℕ, (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) * (reflectedEulerKernel x n : ℂ)‖ ≤
      1 / (x * Real.sqrt x) := by
  have ha :
    ∀ n : ℕ, ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    exact
      (mul_le_mul_of_nonneg_right (χ.norm_le_one n) ArithmeticFunction.vonMangoldt_nonneg).trans_eq
        (one_mul _)
  have hb :=
    norm_tsum_reflectedEulerTerms_le hx (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) ha
  have he :=
    AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_euler_ratio (by norm_num only : (0 : ℝ) < 1)
  norm_num only [Real.rpow_neg_one, one_add_one_eq_two, inv_one, one_pow, Nat.cast_ofNat,
    Real.rpow_two] at he
  have hm :=
    mul_le_mul_of_nonneg_left he (div_nonneg zero_le_one (mul_nonneg hx.le (Real.sqrt_nonneg x)))
  exact hb.trans (by linarith only [hm])

/-- For any Dirichlet character, positive x, and a Gamma line between minus one and zero,
the actual termwise inverse-Mellin Euler series has norm at most 1/(x sqrt x).
Identify every positive-index term with the reflected kernel and discard the zero Mangoldt
term. This is the infinite-series interface; exchange with the full contour integral is separate. -/
theorem norm_twisted_negativeGamma_inversion_tsum_le {q : ℕ} (χ : DirichletCharacter ℂ q) {c x : ℝ}
    (hlo : -1 < c) (hhi : c < 0) (hx : 0 < x) :
    ‖∑' n : ℕ,
          (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) *
            (((1 / ((n : ℝ) * Real.sqrt x) : ℝ) : ℂ) *
              mellinInv c Complex.Gamma (((n : ℝ) * x)⁻¹))‖ ≤
      1 / (x * Real.sqrt x) := by
  have he :
    (fun n : ℕ ↦
        (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) *
          (((1 / ((n : ℝ) * Real.sqrt x) : ℝ) : ℂ) * mellinInv c Complex.Gamma (((n : ℝ) * x)⁻¹))) =
      fun n : ℕ ↦
      (χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) * (reflectedEulerKernel x n : ℂ) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, mul_zero, zero_mul]
    · rw [reflectedEulerKernel_eq_mellinInv hlo hhi hx (Nat.pos_of_ne_zero hn)]
  rw [he]
  exact norm_twisted_reflectedEuler_tsum_le χ hx

end PseudoPrime.Analysis
