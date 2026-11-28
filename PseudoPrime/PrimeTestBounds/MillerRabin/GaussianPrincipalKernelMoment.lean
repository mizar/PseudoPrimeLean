/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianComplexLogPoly
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalCenter
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelSquare
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroCancel
import Mathlib.Tactic.Ring

/-! # The full principal profile moment and the square kernel -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- With zero shift, each profile monomial contributes its matching rational pole. -/
public theorem high_principal_full_moment (K : HighGaussianKernel) {s : ℂ} (hs : 0 < s.re) :
    complexLogPolyMoment K.realProfile 0 s =
      ∑ j ∈ Finset.range (2 * K.degree + 1), (K.expandedCoeff j : ℂ) / s ^ (K.logPower j + 1) := by
  have hm := (complex_log_poly_cutoff K.realProfile 0 hs zero_lt_one).2
  simp only [intervalIntegral.integral_of_le zero_le_one, Complex.ofReal_one, Complex.one_cpow,
    Real.log_one, sub_zero, one_mul, zero_sub] at hm
  rw [← hm]
  let n := K.logPower
  let c := fun j ↦ (K.expandedCoeff j : ℝ) / ((n j).factorial : ℝ)
  let f := fun (j : ℕ) (u : ℝ) ↦ (c j : ℂ) * ((u : ℂ) ^ (s - 1) * ((-Real.log u : ℝ) : ℂ) ^ n j)
  have hf (j : ℕ) : MeasureTheory.IntegrableOn (f j) (Set.Ioc 0 1) :=
    (Analysis.cpow_log_moment (n j) hs).1.const_mul _
  have hfun :
    (fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (K.realProfile.eval (-Real.log u))) = fun u ↦
      ∑ j ∈ Finset.range (2 * K.degree + 1), f j u := by
    funext u
    simp only [HighGaussianKernel.realProfile, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Finset.mul_sum, f, c, n]
    exact Finset.sum_congr rfl (fun j _ ↦ by rw [mul_left_comm])
  rw [hfun, MeasureTheory.integral_finsetSum _ (fun j _ ↦ hf j)]
  apply Finset.sum_congr rfl
  intro j _
  simp only [f, c, n, MeasureTheory.integral_const_mul, (Analysis.cpow_log_moment _ hs).2,
    Complex.ofReal_div, Complex.ofReal_ratCast, Complex.ofReal_natCast]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]

/-- The shifted full principal moment is the square kernel multiplied by the exponential
of five times its pole. The condition is the half-plane of absolute Mellin convergence. -/
public theorem high_principal_moment_kernel (K : HighGaussianKernel) {z : ℂ}
    (hz : 0 < (z + (K.pole : ℂ)).re) :
    let s := z + (K.pole : ℂ)
    (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment K.realProfile 0 s =
      Complex.exp (5 * (K.pole : ℂ)) *
        ((K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
          s ^ (2 * K.degree + 4)) := by
  intro s
  have hn : s ≠ 0 := by
    intro h
    rw [show z + (K.pole : ℂ) = 0 from h, Complex.zero_re] at hz
    exact (lt_irrefl _ hz)
  have hpow : (Real.exp 5 : ℂ) ^ s = Complex.exp (5 * (K.pole : ℂ)) * Complex.exp (5 * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ←
      Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_ofNat]
    change Complex.exp (5 * (z + (K.pole : ℂ))) = _
    rw [mul_add, Complex.exp_add, mul_comm]
  rw [high_principal_full_moment K hz, hpow, mul_assoc, ← high_gaussian_kernel_sum K hn,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The normalized coefficient combines the compact square kernel, the unit-interval
profile moment and the middle endpoint. The factor is the physical profile scaling. -/
public theorem high_principal_coeff_square (K : HighGaussianKernel) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let z := ρ - (1 / 2 : ℂ)
    let s := z + (K.pole : ℂ)
    let E := Complex.exp (-(5 * (K.pole : ℂ)))
    let k :=
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
        s ^ (2 * K.degree + 4)
    E * highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        (k - 4 * (E * complexLogPolyMoment K.realProfile 5 s) +
          4 * (E * (K.realProfile.eval 5 : ℝ)) / ρ) := by
  intro z s E k
  let d := (K.pole : ℝ) - 1 / 2
  have he : (d : ℂ) + ρ = s := by
    dsimp only [d, s, z]
    simp only [Complex.ofReal_sub, Complex.ofReal_ratCast, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat]
    ring
  have hs : 0 < s.re := by
    rw [← he, Complex.add_re, Complex.ofReal_re]
    exact add_pos_of_pos_of_nonneg (sub_pos.mpr (high_gaussian_pole_gt K)) hz.2
  have hf := high_principal_moment_kernel K (z := z) hs
  change
    (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment K.realProfile 0 s =
      Complex.exp (5 * (K.pole : ℂ)) * k at hf
  have hc := high_principal_coeff_cancel K hz hρ
  dsimp only at hc
  change
    highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        ((Real.exp 5 : ℂ) ^ ((d : ℂ) + ρ) * complexLogPolyMoment K.realProfile 0 ((d : ℂ) + ρ) -
            4 * complexLogPolyMoment K.realProfile 5 ((d : ℂ) + ρ) +
          4 * (K.realProfile.eval 5 : ℝ) / ρ) at hc
  rw [he, hf] at hc
  rw [hc]
  have hE : E * Complex.exp (5 * (K.pole : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  calc
    _ =
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
          ((E * Complex.exp (5 * (K.pole : ℂ))) * k -
              4 * (E * complexLogPolyMoment K.realProfile 5 s) +
            4 * (E * (K.realProfile.eval 5 : ℝ)) / ρ) :=
      by ring
    _ = _ := by rw [hE, one_mul]

/-- The middle-to-upper profile integral is the difference between the complete square
kernel and the moment on the unit interval, with the common physical scaling. -/
public theorem high_principal_head_moment (K : HighGaussianKernel) {z : ℂ}
    (hz : 0 < (z + (K.pole : ℂ)).re) :
    let s := z + (K.pole : ℂ)
    let E := Complex.exp (-(5 * (K.pole : ℂ)))
    let k :=
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
        s ^ (2 * K.degree + 4)
    E *
        (∫ u in (1 : ℝ)..Real.exp 5,
          (u : ℂ) ^ (s - 1) * Complex.ofReal (K.realProfile.eval (5 - Real.log u))) =
      k - E * complexLogPolyMoment K.realProfile 5 s := by
  intro s E k
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * Complex.ofReal (K.realProfile.eval (5 - Real.log u))
  have h₁ := complex_log_poly_cutoff K.realProfile 5 hz zero_lt_one
  have h₂ := complex_log_poly_cutoff K.realProfile 5 hz (Real.exp_pos 5)
  have hle : (1 : ℝ) ≤ Real.exp 5 := Real.one_le_exp_iff.mpr (by norm_num only)
  have hi : IntervalIntegrable f MeasureTheory.volume 1 (Real.exp 5) := by
    apply h₂.1.mono_set
    rw [Set.uIcc_of_le hle, Set.uIcc_of_le (Real.exp_pos _).le]
    exact Set.Icc_subset_Icc zero_le_one le_rfl
  have ha := intervalIntegral.integral_add_adjacent_intervals h₁.1 hi
  have hlow : (∫ u in (0 : ℝ)..1, f u) = complexLogPolyMoment K.realProfile 5 s := by
    simpa only [Complex.ofReal_one, Complex.one_cpow, Real.log_one, sub_zero, one_mul] using h₁.2
  have hfull :
    (∫ u in (0 : ℝ)..Real.exp 5, f u) =
      (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment K.realProfile 0 s := by
    simpa only [Real.log_exp, sub_self] using h₂.2
  have hk := high_principal_moment_kernel K (z := z) hz
  change
    (Real.exp 5 : ℂ) ^ s * complexLogPolyMoment K.realProfile 0 s =
      Complex.exp (5 * (K.pole : ℂ)) * k at hk
  change E * (∫ u in (1 : ℝ)..Real.exp 5, f u) = _
  rw [show
      (∫ u in (1 : ℝ)..Real.exp 5, f u) =
        (∫ u in (0 : ℝ)..Real.exp 5, f u) - (∫ u in (0 : ℝ)..1, f u)
      by rw [← ha, add_sub_cancel_left],
    hfull, hlow, hk, mul_sub, ← mul_assoc]
  have hE : E * Complex.exp (5 * (K.pole : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [hE, one_mul]

/-- The centered coefficient in H25 is minus three times the square kernel,
plus four times the head moment and four times the middle value divided by the zero. -/
public theorem high_principal_coeff_head (K : HighGaussianKernel) {ρ : ℂ}
    (hz : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re) (hρ : ρ ≠ 0) :
    let z := ρ - (1 / 2 : ℂ)
    let s := z + (K.pole : ℂ)
    let E := Complex.exp (-(5 * (K.pole : ℂ)))
    let k :=
      (K.normalization : ℂ) * Complex.exp (5 * z) * (K.polynomial.eval₂ (Rat.castHom ℂ) s) ^ 2 /
        s ^ (2 * K.degree + 4)
    let head :=
      E *
        (∫ u in (1 : ℝ)..Real.exp 5,
          (u : ℂ) ^ (s - 1) * Complex.ofReal (K.realProfile.eval (5 - Real.log u)))
    E * highPrincipalFiniteCoeff K ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) *
        (-3 * k + 4 * head + 4 * (E * (K.realProfile.eval 5 : ℝ)) / ρ) := by
  intro z s E k head
  have hs : 0 < (z + (K.pole : ℂ)).re := by
    simp only [z, Complex.add_re, Complex.sub_re, Complex.div_re, Complex.re_ofNat,
      Complex.im_ofNat, Complex.one_re, Complex.one_im, zero_mul, Complex.normSq_ofNat,
      Complex.ratCast_re]
    have hp := high_gaussian_pole_gt K
    linarith only [hp, hz.2]
  have h := high_principal_head_moment K (z := z) hs
  change head = k - E * complexLogPolyMoment K.realProfile 5 s at h
  rw [high_principal_coeff_square K hz hρ, h]
  dsimp only [s, z, E, k]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
