/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaAdaptiveZeroMass
public import PseudoPrime.LLS.GammaVariableScaleBounds

/-! # Adaptive Gamma character bounds with additive zero error 211/10

Use the actual improved zero mass and retain the variable pole and left-moment errors.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH, the Gamma kernel zero-term norm equals the
 nonnegative zero multiplicity times the Gamma norm. Identify the critical-line argument.
 This transfers the adaptive mass bound to actual kernel terms. -/
private theorem norm_gamma_kernelZeroTerm_eq_adaptive {m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ρ : ℂ) :
    ‖gammaMellinKernel.kernelZeroTerm χ ρ‖ =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖ := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · change ‖(D : ℂ) * Complex.Gamma (Complex.I * ρ.im + 1 / 2)‖ = (D : ℝ) * ‖Complex.Gamma ρ‖
    rw [hD]
    norm_num only [Int.cast_zero, zero_mul, norm_zero]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hr := completedLFunction_zero_re_eq_half hGRH hp hne hinv hz
    have he : Complex.I * (ρ.im : ℂ) + 1 / 2 = ρ := by
      apply Complex.ext
      · simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re,
          zero_add]
        exact hr.symm
      · simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
          zero_div, add_zero]
    have hDn : (0 : ℝ) ≤ D := by
      have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
        (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
      exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    change ‖(D : ℂ) * Complex.Gamma (Complex.I * ρ.im + 1 / 2)‖ = _
    rw [he, norm_mul, Complex.norm_intCast, abs_of_nonneg hDn]

/-- Under primitive nonprincipal GRH with nonprincipal inverse and positive scale,
 the actual oscillatory Gamma zero sum has norm below Mlog(m)+211/10.
 Apply absolute convergence and the improved Gamma zero mass.
 This removes the former constant twenty-four from the arithmetic upper input. -/
theorem norm_gamma_oscillatingZeroSum_lt_adaptive {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (11783423 / 25000000 : ℝ) * Real.log m + 211 / 10 := by
  have hs := MellinKernel.summable_oscillatingZeroTerm gammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx ρ).trans
      (norm_gamma_kernelZeroTerm_eq_adaptive hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans_lt
      (AnalyticNumberTheory.DirichletLFunction.gamma_zeroMass_lt_adaptive hm (hGRH m χ hp) hp hne
        hinv)

/-- For primitive conductor 3≤m≤q, q≥20000 and x≥1 under GRH, the real Gamma sum
 is bounded by Mlog(m)+211/10 and the explicit variable-scale remainder.
 Combine the actual zero-sum bound with the completed remainder.
 This retains the primitive conductor and the scale-dependent errors. -/
theorem gamma_primitive_sum_re_le_adaptive_scale {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m + 211 / 10 + 64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gamma_oscillatingZeroSum_lt_adaptive (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := norm_gamma_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz.le, hr, hn, hre]

/-- For a nonprincipal character at q≥20000 under GRH and x≥1, its primitive Gamma
 sum obeys the adaptive upper estimate with its actual conductor and variable remainder.
 Transfer to the primitive source and its inverse. This supplies the improved witness budget. -/
theorem gamma_primitiveCharacter_sum_re_le_adaptive_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 211 / 10 + 64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_adaptive_scale hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

end PseudoPrime.LLS.PaperStatements
