/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaContour
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients

/-! # Gamma derivative expansions for the high Gaussian contour -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected real-gamma contour equals its H33 derivative expansion.
The zeroth coefficient combines the digamma baseline and the reciprocal
difference to evaluate digamma at the shifted kernel pole. -/
theorem high_gamma_reflect_logDeriv (K : HighGaussianKernel) {z : ℝ} (hz : 0 ≤ z) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (l t) * Complex.exp (l t * ((z - 5 : ℝ) : ℂ))
    let d := (K.pole : ℝ) + 1 / 2
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W t)).re =
      Real.exp (-(K.pole : ℝ) * z) *
        (((Complex.digamma ((d / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 * K.realProfile.eval z -
          ∑ j ∈ Finset.range K.realProfile.natDegree,
            v (j + 1) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) := by
  intro l W d v
  let b : ℝ := 17 / 32
  let e := fun t : ℝ ↦ Complex.digamma ((b : ℂ) - Complex.I * (t / 2)) - Complex.digamma (b : ℂ)
  let B := (Complex.digamma (b : ℂ) - Complex.log (Real.pi : ℂ)) / 2
  have hb : 0 < b := by norm_num only [b]
  have hd : 0 < d := by
    dsimp only [d]; linarith only [high_gaussian_pole_gt K]
  have he (t : ℝ) : (1 / 2 - l t) / 2 = (b : ℂ) - Complex.I * (t / 2) := by
    dsimp only [l, b]
    push_cast
    ring
  have hg (t : ℝ) : logDeriv Complex.Gammaℝ (1 / 2 - l t) = B + e t / 2 := by
    have hp : 0 < ((1 / 2 - l t) / 2).re := by
      rw [he]
      norm_num only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_mul, one_mul, sub_zero, b]
    rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat
        (AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp),
      he]
    dsimp only [B, e]
    ring
  have h₀ : -(9 / 16 : ℝ) ≤ -9 / 16 := by norm_num only
  have h₁ : (-9 / 16 : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (-9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  obtain ⟨hW, hiW⟩ := high_gamma_weight_regular K h₀ h₁ hn (Real.exp_pos (z - 5))
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K h₀ h₁ hn (Real.exp_pos (z - 5))
  simp only [high_gamma_weight_exp] at hW hiW hA
  have hi : MeasureTheory.Integrable (fun t ↦ e t * W t) :=
    LLS.PaperStatements.integrable_quadratic_reflected_digamma hb W hW hA
  have hk : (K.pole : ℝ) + (-9 / 16) + 2 * b = d := by
    dsimp only [b, d]
    ring
  have hv := high_gamma_reflect_coefficients K hb h₀ h₁ hn hz (hk.symm ▸ hd)
  simp only [hk, gamma_pole_diff_tsum hb hd] at hv
  simp only [hg, add_mul, div_eq_mul_inv (e _) 2, mul_comm (e _) ((2 : ℂ)⁻¹), mul_assoc]
  rw [MeasureTheory.integral_add (hiW.const_mul B) (hi.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, mul_add, mul_left_comm _ B,
    mul_left_comm _ ((2 : ℂ)⁻¹), high_gamma_weight_integral K h₀ h₁ hn hz]
  change _ = _
  rw [show ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, e t * W t) = _ from hv]
  have hB : B.re = ((Complex.digamma (b : ℂ)).re - Real.log Real.pi) / 2 := by
    dsimp only [B]
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.log_ofReal_re]
  dsimp only [v]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re, hB, neg_mul, Finset.sum_neg_distrib]
  ring

/-- A forward reciprocal factor with positive real base is integrable
against a continuous, integrable weight with quadratic decay. -/
private theorem high_gamma_inv_integrable {A b : ℝ} (hb : 0 < b) (W : ℝ → ℂ) (hW : Continuous W)
    (hiW : MeasureTheory.Integrable W) (hA : ∀ t : ℝ, ‖W t‖ ≤ A / (1 + t ^ 2)) :
    MeasureTheory.Integrable (fun t : ℝ ↦ (1 / ((b : ℂ) + Complex.I * (t : ℂ) / 2)) * W t) := by
  have h :=
    (hiW.const_mul (1 / (b : ℂ))).sub
      (LLS.PaperStatements.quadratic_resolvent_integral_bound hb W hW hA).1
  simpa only [Pi.sub_def, sub_mul, sub_sub_cancel, mul_div_assoc] using h

/-- Separate the two low forward gamma poles before expanding the regular
digamma term. Both poles are kept as finite convolution moments. -/
theorem high_gamma_forward_split (K : HighGaussianKernel) {z : ℝ} (hz : 0 ≤ z) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    let b : ℝ := 81 / 32
    let E := Real.exp (-(K.pole : ℝ) * z)
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W t) =
      ((Complex.digamma (b : ℂ) - Complex.log (Real.pi : ℂ)) / 2) *
            ((E * K.realProfile.eval z : ℝ) : ℂ) +
          (2 : ℂ)⁻¹ *
            (D *
              (∫ t : ℝ,
                (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
                  W t)) -
        (E : ℂ) *
          ((∫ v in (0 : ℝ)..z, Real.exp (((K.pole : ℝ) - 1 / 2) * (z - v)) * K.realProfile.eval v :
              ℝ) :
            ℂ) -
        (E : ℂ) *
          ((∫ v in (0 : ℝ)..z, Real.exp (((K.pole : ℝ) - 5 / 2) * (z - v)) * K.realProfile.eval v :
              ℝ) :
            ℂ) := by
  intro r W b E D
  let B := (Complex.digamma (b : ℂ) - Complex.log (Real.pi : ℂ)) / 2
  let e := fun t : ℝ ↦ Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)
  have h₀ : -(9 / 16 : ℝ) ≤ 9 / 16 := by norm_num only
  have hn : (9 / 16 : ℝ) ≠ -1 / 2 := by norm_num only
  obtain ⟨hW, hiW⟩ := high_gamma_weight_regular K h₀ le_rfl hn (Real.exp_pos (z - 5))
  obtain ⟨A, hA⟩ := high_gamma_weight_quadratic K h₀ le_rfl hn (Real.exp_pos (z - 5))
  simp only [high_gamma_weight_exp] at hW hiW hA
  have hb : 0 < b := by norm_num only [b]
  have hi : MeasureTheory.Integrable (fun t ↦ e t * W t) := by
    let Wn := fun t : ℝ ↦ W (-t)
    have h :=
      (LLS.PaperStatements.integrable_quadratic_reflected_digamma hb Wn (hW.comp continuous_neg)
          (fun t ↦ by simpa only [neg_sq] using hA (-t))).comp_neg
    simpa only [Wn, e, neg_neg, Complex.ofReal_neg, neg_div, mul_neg, sub_neg_eq_add] using h
  have hP (q : ℝ) (hq : -(9 / 16 : ℝ) < q) :
    MeasureTheory.Integrable (fun t : ℝ ↦ (r t + (q : ℂ))⁻¹ * W t) := by
    let bq := (9 / 16 + q) / 2
    have hbq : 0 < bq := by
      dsimp only [bq]; linarith only [hq]
    have heq (t : ℝ) :
      (r t + (q : ℂ))⁻¹ = (2 : ℂ)⁻¹ * (1 / ((bq : ℂ) + Complex.I * (t : ℂ) / 2)) := by
      rw [one_div, ← mul_inv]
      congr 1
      dsimp only [r, bq]
      push_cast
      ring
    simpa only [heq, mul_assoc] using
      (high_gamma_inv_integrable hbq W hW hiW hA).const_mul ((2 : ℂ)⁻¹)
  have hp₁ : MeasureTheory.Integrable (fun t : ℝ ↦ (r t + 1 / 2)⁻¹ * W t) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      hP (1 / 2) (by norm_num only)
  have hp₂ : MeasureTheory.Integrable (fun t : ℝ ↦ (r t + 5 / 2)⁻¹ * W t) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using hP (5 / 2) (by norm_num only)
  rw [gamma_forward_integral_split W hiW hi hp₁ hp₂, mul_sub, mul_sub, mul_add, mul_left_comm _ B,
    mul_left_comm _ ((2 : ℂ)⁻¹)]
  dsimp only [D]
  rw [high_gamma_weight_integral K h₀ le_rfl hn hz]
  have h₁ := high_gamma_forward_pole K (q := 1 / 2) (by norm_num only) hz hW hiW
  have h₂ := high_gamma_forward_pole K (q := 5 / 2) (by norm_num only) hz hW hiW
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
    intervalIntegral.integral_ofReal] at h₁ h₂
  dsimp only [r, W]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [h₁, h₂]
  simp only [B, b, E, Complex.ofReal_div, Complex.ofReal_ofNat]

/-- The forward real-gamma contour equals the H33 derivative expansion
minus the two low-pole moments and the convergent trivial-zero tail. -/
theorem high_gamma_forward_logDeriv (K : HighGaussianKernel) {z : ℝ} (hz : 0 < z) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let W := fun t ↦ highGaussianSquare K (r t) * Complex.exp (r t * ((z - 5 : ℝ) : ℂ))
    let a := (K.pole : ℝ)
    let d := 9 / 2 - a
    let v := fun j : ℕ ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    (((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W t)).re =
      Real.exp (-a * z) *
          (((Complex.digamma ((d / 2 : ℝ) : ℂ)).re - Real.log Real.pi) / 2 * K.realProfile.eval z -
            ∑ j ∈ Finset.range K.realProfile.natDegree,
              ((-1 : ℝ) ^ (j + 1) * v (j + 1)) * (∑' n : ℕ, 1 / (d + 2 * n) ^ (j + 2))) -
        Real.exp (-z / 2) *
          (∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-(a - 1 / 2) * t)) -
        Real.exp (-a * z) *
          (∫ t in (0 : ℝ)..z, Real.exp ((a - 5 / 2) * (z - t)) * K.realProfile.eval t) -
        Real.exp (-a * z) *
          (∑' n : ℕ, Real.exp (-(d + 2 * n) * z) * highProfileLaplace K (-(d + 2 * n))) := by
  intro r W a d v
  let b : ℝ := 81 / 32
  have hb : 0 < b := by norm_num only [b]
  have hd : 1 ≤ d := by
    dsimp only [d, a]
    cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hk : 2 * b - (9 / 16 : ℝ) - (K.pole : ℝ) = d := by
    dsimp only [b, d, a]
    ring
  have hv :=
    high_gamma_forward_coefficients K (c := 9 / 16) hb (by norm_num only) le_rfl (by norm_num only)
      hz (hk.symm ▸ hd)
  simp only [hk, gamma_pole_diff_tsum hb (zero_lt_one.trans_le hd)] at hv
  rw [high_gamma_forward_split K hz.le, hv]
  have hJ :
    Real.exp (-a * z) *
        (∫ t in (0 : ℝ)..z, Real.exp ((a - 1 / 2) * (z - t)) * K.realProfile.eval t) =
      Real.exp (-z / 2) *
        (∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-(a - 1 / 2) * t)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add, mul_comm (K.realProfile.eval t), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  let B := (Complex.digamma (b : ℂ) - Complex.log (Real.pi : ℂ)) / 2
  have hB : B.re = ((Complex.digamma (b : ℂ)).re - Real.log Real.pi) / 2 := by
    dsimp only [B]
    rw [Complex.div_ofNat_re, Complex.sub_re, Complex.log_ofReal_re]
  change (B * _ + _ - _ - _).re = _
  dsimp only [v, a] at *
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.add_re, Complex.sub_re, hB, neg_mul,
    Finset.sum_neg_distrib]
  simp only [neg_mul] at hJ ⊢
  rw [hJ]
  ring

/-- The H33 coefficients multiplying derivatives of the physical profile.
The constant uses the two digamma values, and higher orders use their
convergent reciprocal-power series. -/
noncomputable def highGammaCoeff (K : HighGaussianKernel) : ℕ → ℝ
  | 0 =>
    ((Complex.digamma (((9 / 2 - (K.pole : ℝ)) / 2 : ℝ) : ℂ)).re +
          (Complex.digamma ((((K.pole : ℝ) + 1 / 2) / 2 : ℝ) : ℂ)).re) /
        2 -
      Real.log Real.pi
  | j + 1 =>
    -(((-1 : ℝ) ^ (j + 1)) * (∑' n : ℕ, 1 / (9 / 2 - (K.pole : ℝ) + 2 * n) ^ (j + 2)) +
        ∑' n : ℕ, 1 / ((K.pole : ℝ) + 1 / 2 + 2 * n) ^ (j + 2))

/-- The common contour in H33 is the finite gamma derivative sum minus
the two low-pole moments and the nonnegative remaining trivial-zero series. -/
theorem high_common_contour_h33 (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {z : ℝ} (hz : 0 < z) :
    let a := (K.pole : ℝ)
    let I := ∫ t in (0 : ℝ)..z, Real.exp ((a - 5 / 2) * (z - t)) * K.realProfile.eval t
    let J := ∫ t in (0 : ℝ)..z, K.realProfile.eval t * Real.exp (-(a - 1 / 2) * t)
    highCommonContour K (Real.exp (z - 5)) =
      Real.exp (-a * z) *
          ((∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
              highGammaCoeff K j * ((Polynomial.derivative^[j]) K.realProfile).eval z) -
            I) -
        Real.exp (-z / 2) * J -
        ∑' n : ℕ,
          Real.exp (-((1 / 2 : ℝ) + 2 * (n + 2)) * z) *
            highProfileLaplace K (a - 1 / 2 - 2 * (n + 2)) := by
  intro a I J
  have h := high_common_contour_gamma K hp hn hi he (Real.exp_pos (z - 5))
  have hγ : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ :=
    funext AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def
  have hw (t : ℝ) :
    ((17 / 16 : ℝ) : ℂ) - Complex.I * t = 1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) := by
    push_cast
    ring
  dsimp only at h
  rw [hγ] at h
  simp only [high_gamma_weight_exp, hw] at h
  rw [h, high_gamma_forward_logDeriv K hz, high_gamma_reflect_logDeriv K hz.le]
  have hT :
    Real.exp (-(K.pole : ℝ) * z) *
        (∑' n : ℕ,
          Real.exp (-(9 / 2 - (K.pole : ℝ) + 2 * n) * z) *
            highProfileLaplace K (-(9 / 2 - (K.pole : ℝ) + 2 * n))) =
      ∑' n : ℕ,
        Real.exp (-((1 / 2 : ℝ) + 2 * (n + 2)) * z) *
          highProfileLaplace K ((K.pole : ℝ) - 1 / 2 - 2 * (n + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [← mul_assoc, ← Real.exp_add]
    congr 2 <;> ring
  dsimp only [I, J, a]
  rw [hT, Finset.sum_range_succ']
  simp only [highGammaCoeff, Function.iterate_zero_apply, neg_add, add_mul, neg_mul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_assoc, mul_comm, mul_left_comm]
  ring

/-- Turn H33 into an upper bound on the common contour over a finite cell
using a pointwise profile lower bound and enclosures for the gamma coefficients. -/
theorem high_common_contour_cell_le (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {x z M : ℝ} (hxz : x ≤ z) (hz : 0 < z) (hM : 0 ≤ M)
    (hB : ∀ t ∈ Set.Icc x z, -M ≤ K.realProfile.eval t) {l u : ℕ → ℝ}
    (hg :
      ∀ j ∈ Finset.range (K.realProfile.natDegree + 1),
        l j ≤ highGammaCoeff K j ∧ highGammaCoeff K j ≤ u j) :
    let a := (K.pole : ℝ)
    let s := a - 5 / 2
    let d := a - 1 / 2
    let B := fun j ↦ ((Polynomial.derivative^[j]) K.realProfile).eval z
    let I := ∫ t in (0 : ℝ)..x, Real.exp (s * (x - t)) * K.realProfile.eval t
    let J := ∫ t in (0 : ℝ)..x, K.realProfile.eval t * Real.exp (-d * t)
    highCommonContour K (Real.exp (z - 5)) ≤
      Real.exp (-a * z) *
          (∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
            (u j * B j + (u j - l j) * max (-B j) 0)) +
        Real.exp (-a * z) * (Real.exp (s * (z - x)) * (max (-I) 0 + (z - x) * M)) +
        Real.exp (-z / 2) * (max (-J) 0 + (z - x) * (Real.exp (-d * x) * M)) := by
  intro a s d B I J
  have hs : 0 ≤ s := by
    dsimp only [s, a]
    cases K <;> norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hd : 0 ≤ d := sub_nonneg.mpr (high_gaussian_pole_gt K).le
  rw [high_common_contour_h33 K hp hn hi he hz]
  exact high_gamma_cell_expression_le K hxz hs hd hM hB (Real.exp_pos _).le (Real.exp_pos _).le _ hg

end PseudoPrime.PrimeTestBounds.MillerRabin
