/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveLogWeightedNormBounds

/-! # Bounds for the completed logarithmic derivative at zero

Conjugation identifies the norms for a primitive character and its inverse.
The reciprocal explicit formula can then bound the endpoint by an arithmetic sum.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a primitive nonprincipal character, the xi logarithmic derivative at zero
for the inverse character is the conjugate of the original endpoint. Conjugate
the completed value and derivative, then add the real scaling term `log q/2`.
This allows both endpoints in the reciprocal formula to use one norm. -/
theorem logDeriv_xi_inv_zero_eq_conj {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) :
    logDeriv (xi χ⁻¹) 0 = starRingEnd ℂ (logDeriv (xi χ) 0) := by
  have hv := AnalyticNumberTheory.DirichletLFunction.DirichletCharacter.completedLFunction_conj χ 0
  simp only [map_zero] at hv
  have hd :=
    AnalyticNumberTheory.DirichletLFunction.DirichletCharacter.deriv_completedLFunction_zero_conj
      hne
  have hc :
    logDeriv χ⁻¹.completedLFunction 0 = starRingEnd ℂ (logDeriv χ.completedLFunction 0) := by
    rw [logDeriv_apply, logDeriv_apply, ← hv, ← hd, ← map_div₀]
  have hpi := AnalyticNumberTheory.DirichletLFunction.DirichletCharacter.isPrimitive_inv hp
  have hl : Complex.log (q : ℂ) = (Real.log (q : ℝ) : ℂ) :=
    (Complex.ofReal_log (Nat.cast_nonneg q)).symm
  rw [logDeriv_xi_zero_eq hpi (inv_ne_one.mpr hne), logDeriv_xi_zero_eq hp hne, hc, hl]
  simp only [map_add, map_div₀, map_ofNat, Complex.conj_ofReal]

/-- For a primitive nonprincipal character, the two xi endpoints have equal norms.
Apply norm invariance under conjugation to the endpoint identity. This is the norm
symmetry used when bounding the complex reciprocal formula. -/
theorem norm_logDeriv_xi_inv_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) : ‖logDeriv (xi χ⁻¹) 0‖ = ‖logDeriv (xi χ) 0‖ := by
  rw [logDeriv_xi_inv_zero_eq_conj hp hne, Complex.norm_conj]

/-- Under GRH, for a primitive character of modulus at least three, the absolute
real Hadamard constant is at most the norm of its xi endpoint. The endpoint real
part is minus that absolute constant. This removes zero mass from a norm estimate. -/
theorem abs_primitiveBRe_le_norm_logDeriv_xi_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ ‖logDeriv (xi χ) 0‖ := by
  have h := Complex.abs_re_le_norm (logDeriv (xi χ) 0)
  rw [re_logDeriv_xi_zero_eq_neg_abs_BRe hq hp hGRH, abs_neg, abs_abs] at h
  exact h

/-- For a primitive character of modulus at least three under GRH and cutoff above
one, the xi endpoint norm times `1-1/x-2/sqrt x` is bounded by the reciprocal sum
norm and the absolute conductor-parity term. Use the reciprocal explicit formula,
equal endpoint norms and the zero-mass norm bound. At cutoff 100 the left factor
is 79/100, as used before equation (4.6). -/
theorem norm_logDeriv_xi_zero_mul_reciprocal_factor_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖logDeriv (xi χ) 0‖ * (1 - 1 / x - 2 / Real.sqrt x) ≤
      ‖AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ‖ +
        |1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ x| := by
  let D := logDeriv (xi χ) 0
  let Di := logDeriv (xi χ⁻¹) 0
  let S := AnalyticNumberTheory.Arithmetic.characterReciprocalWeightedSum x χ
  let c : ℝ := 1 / 2 * (1 - 1 / x) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ x
  let e := S - Di - (1 / (x : ℂ)) * D - (c : ℂ)
  have he := norm_characterReciprocalWeightedSum_error_le hq hp hGRH hx
  have hD := norm_logDeriv_xi_inv_zero hp (primitiveCharacter_ne_one_of_three_le hq hp)
  have hB := abs_primitiveBRe_le_norm_logDeriv_xi_zero hq hp hGRH
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hBs :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB (by norm_num only : (0 : ℝ) ≤ 2)) hs.le
  have ht1 := norm_sub_le (Di + (1 / (x : ℂ)) * D) ((1 / (x : ℂ)) * D)
  rw [add_sub_cancel_right] at ht1
  have hid : Di + (1 / (x : ℂ)) * D = (S - (c : ℂ)) - e := by
    dsimp only [e]
    ring
  rw [hid] at ht1
  have ht2 := norm_sub_le (S - (c : ℂ)) e
  have ht3 := norm_sub_le S (c : ℂ)
  simp only [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx0] at ht1
  rw [Complex.norm_real, Real.norm_eq_abs] at ht3
  change ‖e‖ ≤ _ at he
  change ‖Di‖ = ‖D‖ at hD
  change ‖D‖ * (1 - 1 / x - 2 / Real.sqrt x) ≤ ‖S‖ + |c|
  change _ ≤ 2 * ‖D‖ / Real.sqrt x at hBs
  simp only [div_eq_mul_inv] at ht1 he hBs ⊢
  nlinarith only [ht1, ht2, ht3, he, hD, hBs]

/-- At cutoff 100, GRH bounds a primitive character's xi endpoint using a finite
real Mangoldt sum and its explicit parity correction. The reciprocal factor is
79/100; removing character values gives the real arithmetic majorant. This is
the finite numerical input required to obtain equation (4.6). -/
theorem norm_logDeriv_xi_zero_le_cutoff100 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ‖logDeriv (xi χ) 0‖ ≤
      (100 / 79 : ℝ) *
        (AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtSum 100 +
          |(99 / 200 : ℝ) * Real.log ((q : ℝ) / Real.pi) + reciprocalCorrection χ 100|) := by
  have h := norm_logDeriv_xi_zero_mul_reciprocal_factor_le hq hp hGRH (x := 100) (by norm_num only)
  have hs :=
    AnalyticNumberTheory.Arithmetic.norm_characterReciprocalWeightedSum_le χ (x := 100)
      (by norm_num only)
  norm_num only at h
  nlinarith only [h, hs]

end PseudoPrime.LLS.PaperStatements
