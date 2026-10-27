/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaZeroMass
public import PseudoPrime.LLS.GammaSharpVariableScaleBounds

/-! # Two-pole Gamma zero bounds in the arithmetic explicit formula -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH, the Gamma zero-term norm equals the nonnegative
 zero multiplicity times the actual Gamma norm. Identify its critical-line argument.
 This transfers any certified prefix mass bound to the kernel terms. -/
theorem norm_gamma_kernelZeroTerm_eq_twoPole {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
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

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data at any positive scale, bound the actual
oscillating Gamma zero sum by the signed two-pole mass with retained Euler prefixes.
Use absolute convergence and identify the critical-line kernel norm. This connects
the new zero-mass estimate to the Mellin explicit formula. -/
theorem norm_gamma_oscillatingZeroSum_le_twoPole {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (A B : Finset ℕ) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      Real.log m / 2 + 419 / 50 - (∑ n ∈ A, realPairedEulerTerm χ (5 / 4) n) -
        (3 / 4 : ℝ) * (∑ n ∈ B, Real.log n * realPairedEulerTerm χ (11 / 4) n) := by
  have hs := MellinKernel.summable_oscillatingZeroTerm gammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx ρ).trans
      (norm_gamma_kernelZeroTerm_eq_twoPole hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact hn.trans (gamma_zeroMass_le_twoPole_rational_retained hm (hGRH m χ hp) hp hne hinv A B).2

open AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH with primitive conductor between three and an ambient modulus at
least 20000, bound the Gamma arithmetic sum at scales at least one. Combine the
two-pole zero bound with the existing explicit remainder, retaining both Euler
prefix savings. This is the arithmetic consumer for finite-scale comparisons. -/
theorem gamma_primitive_sum_re_le_twoPole {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + 419 / 50 - (∑ n ∈ A, realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) * (∑ n ∈ B, Real.log n * realPairedEulerTerm χ (11 / 4) n) +
        64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log m + 28) + 1) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole (by linarith only [hm]) hGRH hp hne hinv
      (zero_lt_one.trans_le hx) A B
  have hr := norm_gamma_primitive_remainder_le_variable_scale_sharp hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz, hr, hn, hre]

/-- For primitive nonprincipal GRH data of modulus at least eight, bound the
completed Gamma remainder at every scale at least one. Use the same-modulus pole
estimate and the existing left moments. This removes the ambient-modulus 20000
gate when no smaller-conductor transfer is requested. -/
theorem norm_gamma_primitive_remainder_le_from_eight {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 8 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, gammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      64 / 9 + ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gammaMellinKernel (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x
      (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := hx
  have hr : ‖S - (P - Z + J)‖ ≤ 64 / 9 :=
    norm_gamma_completed_remainder_le_sixty_four_ninths (by linarith only [hq]) hGRH hp hne hinv
      (a := -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
  have hP0 := gamma_poleResidue_le_affine_log hq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x := hP0
  have hJ : ‖J‖ ≤ x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) :=
    norm_gamma_left_integral_le_sharp_moments hp hne hinv (zero_lt_one.trans_le hx)
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + J)) P
  have hn2 := norm_add_le ((S - (P - Z + J)) + P) J
  linarith only [hr, hP, hJ, hn1, hn2]

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data of modulus at least eight, the two-pole
Gamma arithmetic bound holds at every scale at least one, with both Euler prefix
savings retained. Combine the oscillating zero bound with the same-modulus
remainder estimate. This lowers the start for the primitive arithmetic interface. -/
theorem gamma_primitive_sum_re_le_twoPole_from_eight {q : ℕ} [NeZero q] (hq : 8 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log q / 2 + 419 / 50 - (∑ n ∈ A, realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) * (∑ n ∈ B, Real.log n * realPairedEulerTerm χ (11 / 4) n) +
        64 / 9 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) := by
  let S := ∑' n : ℕ, gammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole (by linarith only [hq]) hGRH hp hne hinv
      (zero_lt_one.trans_le hx) A B
  have hr := norm_gamma_primitive_remainder_le_from_eight hq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  linarith only [hz, hr, hn, hre]

end PseudoPrime.LLS.PaperStatements
