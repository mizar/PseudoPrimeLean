/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassMellin
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassTransform
import PseudoPrime.Analysis.TriangularDigammaMoments
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! # Vertical Mellin inversion for the high Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Squared norm of a vertical complex coordinate in the orientation used for Mellin inversion. -/
private theorem vertical_norm_sq (b t : ℝ) :
    ‖(b : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 = b ^ 2 + t ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_add, mul_one, add_zero,
    pow_two]

/-- Taking the smaller of the two distances to the poles gives a Cauchy denominator. -/
private theorem vertical_product_bound {b d e t : ℝ} (hb : 0 < b) (hd : b ≤ d) (he : b ≤ e) :
    b ^ 2 + t ^ 2 ≤ ‖(d : ℂ) + (t : ℂ) * Complex.I‖ * ‖(e : ℂ) + (-t : ℝ) * Complex.I‖ := by
  let r := ‖(b : ℂ) + (t : ℂ) * Complex.I‖
  have h₁ : r ≤ ‖(d : ℂ) + (t : ℂ) * Complex.I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [vertical_norm_sq, vertical_norm_sq]
    exact add_le_add (pow_le_pow_left₀ hb.le hd 2) le_rfl
  have h₂ : r ≤ ‖(e : ℂ) + (-t : ℝ) * Complex.I‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [vertical_norm_sq, vertical_norm_sq, neg_sq]
    exact add_le_add (pow_le_pow_left₀ hb.le he 2) le_rfl
  rw [← vertical_norm_sq b t, pow_two]
  exact mul_le_mul h₁ h₂ (norm_nonneg _) (norm_nonneg _)

/-- The two shifted poles on a vertical line give an integrable reciprocal product
for every positive common order. -/
private theorem integrable_vertical_pair {d e : ℝ} (hd : 0 < d) (he : 0 < e) (m : ℕ) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        1 /
          (((d : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1) *
            ((e : ℂ) + (-t : ℝ) * Complex.I) ^ (m + 1))) := by
  let b := min d e
  have hb : 0 < b := lt_min hd he
  have hB (t : ℝ) := vertical_product_bound hb (min_le_left d e) (min_le_right d e) (t := t)
  have hs (t : ℝ) : 0 < b ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hb 2) (sq_nonneg t)
  have nz (t : ℝ) :
    ((d : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1) * ((e : ℂ) + (-t : ℝ) * Complex.I) ^ (m + 1) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_mul, norm_pow, norm_pow, ← mul_pow]
    exact pow_pos ((hs t).trans_le (hB t)) _
  apply ((Analysis.integrable_cauchy_of_pos hb).const_mul ((b ^ 2) ^ m)⁻¹).mono'
  · apply Continuous.aestronglyMeasurable
    apply continuous_const.div _ nz
    fun_prop
  · apply Filter.Eventually.of_forall
    intro t
    simp only [one_div, norm_inv, norm_mul, norm_pow, ← mul_pow, ← mul_inv_rev]
    rw [mul_comm (b ^ 2 + t ^ 2) ((b ^ 2) ^ m)]
    apply inv_anti₀ (mul_pos (pow_pos (pow_pos hb 2) m) (hs t))
    rw [pow_succ]
    exact
      mul_le_mul
        (pow_le_pow_left₀ (sq_nonneg b) ((le_add_of_nonneg_right (sq_nonneg t)).trans (hB t)) m)
        (hB t) (hs t).le (pow_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _)

/-- The high Gaussian absolute mass is integrable on each vertical line between its two poles. -/
public theorem high_gaussian_mass_vertical (K : HighGaussianKernel) {c : ℝ} (hl : -(K.pole : ℝ) < c)
    (hr : c < (K.pole : ℝ)) : Complex.VerticalIntegrable K.massExtension c := by
  have hre (t : ℝ) : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero]
  have hs (t : ℝ) :=
    high_gaussian_mass_extension_sum K (z := (c : ℂ) + (t : ℂ) * Complex.I)
      (by
        rw [hre]; exact hl)
      (by
        rw [hre]; exact hr)
  unfold Complex.VerticalIntegrable
  simp only [hs]
  apply MeasureTheory.integrable_finsetSum
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hn : 0 < K.degree + 2 - j :=
    Nat.sub_pos_of_lt (hj'.trans_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hd : 0 < (K.pole : ℝ) + c := by linarith only [hl]
  have he : 0 < (K.pole : ℝ) - c := sub_pos.mpr hr
  have h :=
    (integrable_vertical_pair hd he m).const_mul
      ((K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ))
  apply h.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [hm, Complex.ofReal_add, Complex.ofReal_ratCast, Complex.ofReal_neg, mul_one_div,
    ← add_assoc, neg_mul, sub_eq_add_neg]
  have hdif :
    (K.pole : ℂ) + -(c : ℂ) + -((t : ℂ) * Complex.I) =
      (K.pole : ℂ) + -((c : ℂ) + (t : ℂ) * Complex.I) := by
    ring
  rw [hdif]

/-- Pointwise Mellin inversion of the signed high Gaussian mass profile
holds throughout the open strip between the two poles. -/
public theorem high_gaussian_mass_inversion (K : HighGaussianKernel) {c u : ℝ}
    (hl : -(K.pole : ℝ) < c) (hr : c < (K.pole : ℝ)) (hu : 0 < u) :
    Analysis.inverseMellin K.massExtension c u = (K.massProfile u : ℂ) := by
  let f := fun v : ℝ ↦ (K.massProfile v : ℂ)
  have hre (t : ℝ) : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero]
  have h (t : ℝ) :
    HasMellin f ((c : ℂ) + (t : ℂ) * Complex.I) (K.massExtension ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    high_gaussian_mass_hasMellin K
      (by
        rw [hre]; exact hl)
      (by
        rw [hre]; exact hr)
  have hi :=
    (high_gaussian_mass_vertical K hl hr).congr (Filter.Eventually.of_forall fun t ↦ (h t).2.symm)
  have h0 : MellinConvergent f (c : ℂ) := by
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using (h 0).1
  have hc : ContinuousAt f u :=
    Complex.continuous_ofReal.continuousAt.comp (high_gaussian_mass_profile_cont K hu)
  change Analysis.inverseMellin K.massExtension c u = f u
  rw [Analysis.inverseMellin_eq_mellinInv, ← mellinInv_mellin_eq c f hu h0 hi hc]
  unfold mellinInv
  congr 1
  exact
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun t ↦
        congrArg (fun z : ℂ ↦ (u : ℂ) ^ (-((c : ℂ) + t * Complex.I)) • z) (h t).2.symm)

/-- At positive arguments, the signed Mellin profile is the reciprocal
Fourier mass profile evaluated at the absolute logarithm. -/
public theorem high_gaussian_mass_profile_log (K : HighGaussianKernel) {u : ℝ} (hu : 0 < u) :
    K.massProfile u =
      1 / 2 * Real.exp (-(K.pole : ℝ) * |Real.log u|) *
        (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) |Real.log u| := by
  have ha := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have h := high_gaussian_mass_inversion K (c := 0) (neg_lt_zero.mpr ha) ha hu
  have hphase (t : ℝ) :
    (u : ℂ) ^ (-(Complex.I * (t : ℂ))) = Complex.exp (((-Real.log u * t : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), ← Complex.ofReal_log hu.le,
      Complex.ofReal_mul, Complex.ofReal_neg]
    congr 1
    ring
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_zero, zero_add, high_gaussian_mass_extension_line, hphase] at h
  rw [high_gaussian_mass_transform] at h
  have he := Complex.ofReal_injective (by simpa only [← Complex.ofReal_mul, abs_neg] using h)
  rw [← he]
  have hπ : (Real.pi : ℝ) / Real.pi = 1 := div_self Real.pi_ne_zero
  linear_combination
    (1 / 2 * Real.exp (-(K.pole : ℝ) * |Real.log u|) *
        (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) |Real.log u|) *
      hπ

/-- The value of the Mellin profile at its central argument is the conductor coefficient. -/
public theorem high_gaussian_mass_profile_one (K : HighGaussianKernel) :
    K.massProfile 1 = 3 / 16 := by
  rw [high_gaussian_mass_profile_log K zero_lt_one]
  simp only [Real.log_one, abs_zero, mul_zero, Real.exp_zero, mul_one,
    high_gaussian_mass_polynomial_zero]
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
