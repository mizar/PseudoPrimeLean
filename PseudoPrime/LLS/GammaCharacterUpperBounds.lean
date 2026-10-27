/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrimitiveRemainderBounds
public import PseudoPrime.LLS.MellinKernelPrimitiveAverage
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaResolventZeroMass

/-! # Numerical nonprincipal Gamma arithmetic upper bounds

The actual oscillatory zero sum has the certified Gamma zero-mass bound.
Combining it with the explicit remainder retains the primitive conductor term.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH data, the Gamma kernel zero-term norm
equals the completed zero multiplicity times norm(Gamma rho). A nonzero divisor
lies on the critical line, where the shifted Gamma argument equals rho.
This identifies the actual kernel zero mass with the numerical Gamma estimate. -/
private theorem norm_gamma_kernelZeroTerm_eq {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (ρ : ℂ) :
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

/-- Under primitive nonprincipal GRH data with nonprincipal inverse and
positive scale, the oscillatory Gamma zero sum has norm below
11783423/25000000 times log(m) plus 24. Its phase has norm one; absolute
convergence and the numerical Gamma zero mass supply the bound.
This keeps the conductor coefficient in the fixed-kernel explicit formula. -/
theorem norm_gamma_oscillatingZeroSum_lt {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ <
      (11783423 / 25000000 : ℝ) * Real.log m + 24 := by
  have hs := MellinKernel.summable_oscillatingZeroTerm gammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx ρ).trans
      (norm_gamma_kernelZeroTerm_eq hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans_lt
      (AnalyticNumberTheory.DirichletLFunction.gamma_zeroMass_lt hm (hGRH m χ hp) hp hne hinv)

/-- For primitive nonprincipal conductor 3≤m≤q, ambient q≥20000 and x≥1
under GRH, the real Gamma arithmetic sum is at most
M log(m)+39+(10002log(q)+10004)/sqrt(x), where M=11783423/25000000.
Combine the oscillatory zero bound with the explicit contour remainder.
The conductor is retained separately from the ambient remainder error. -/
theorem gamma_primitive_sum_re_le_explicit {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m + 39 + (10002 * Real.log q + 10004) / Real.sqrt x := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hz :=
    norm_gamma_oscillatingZeroSum_lt (by linarith only [hm]) hGRH hp hne hinv
      (zero_lt_one.trans_le hx)
  have hr := norm_gamma_primitive_remainder_le_explicit hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz.le, hr, hn, hre]

/-- For any nonprincipal character of level q≥20000 under GRH and x≥1,
the primitive Gamma sum has the numerical upper bound with leading term
M log(conductor), additive 39 and explicit ambient inverse-square-root error.
The conductor is at least three and at most q; its primitive source and inverse
are nonprincipal. This supplies every nonprincipal term in subgroup averaging. -/
theorem gamma_primitiveCharacter_sum_re_le_explicit {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 39 +
        (10002 * Real.log q + 10004) / Real.sqrt x := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_explicit hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

end PseudoPrime.LLS.PaperStatements
