/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassMellin
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole
import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula
import PseudoPrime.LLS.PaperStatements.MellinKernelArithmeticMellin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Absolute zero mass in terms of the combined Mellin profile -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem mass_integrand (K : HighGaussianKernel) {z : ℂ} (hl : -(K.pole : ℝ) < z.re)
    (hr : z.re < (K.pole : ℝ)) (g : ℂ) :
    (∑ j ∈ Finset.range (K.degree + 1),
        ((K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)) *
          (g *
            (balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)).function
              z)) =
      g * K.massExtension z := by
  rw [high_gaussian_balanced_sum K hl hr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _

private theorem mass_arithmetic (K : HighGaussianKernel) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (n : ℕ) :
    (∑ j ∈ Finset.range (K.degree + 1),
        ((K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)) *
          (balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)).summand χ 1
            n) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n * (K.massProfile n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, mul_zero, Finset.sum_const_zero,
      Nat.cast_zero, Real.sqrt_zero, div_zero, Complex.ofReal_zero, zero_mul]
  have hu : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have ha := high_gaussian_pole_ge_two K
  have hl : -(K.pole : ℝ) < 0 := by linarith only [ha]
  have hr : 0 < (K.pole : ℝ) := by linarith only [ha]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, div_one,
    LLS.PaperStatements.MellinKernel.transform, balanced_pole_inverse ha _ hl hr hu,
    HighGaussianKernel.massProfile, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : K.degree + 1 - j + 1 = K.degree + 2 - j :=
    (Nat.sub_add_comm (hj'.trans (Nat.le_succ K.degree))).symm
  rw [hm]
  simp only [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ratCast, div_eq_mul_inv]
  ring

/-- The absolute zero mass equals the two contour integrals of the combined
mass function minus the unit-scale Mangoldt series of its signed profile. -/
public theorem high_gaussian_mass_profile_contours (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    {x : ℝ} (hx : 0 < x) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    ((∑' ρ : ℂ, ‖K.zeroTerm χ x ρ‖ : ℝ) : ℂ) =
      d * (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * K.massExtension (l t)) +
          d * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * K.massExtension (r t)) -
        (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (K.massProfile n : ℂ)) := by
  intro l r d
  have h := high_gaussian_mass_zero_contours K hq hg hp hne
  dsimp only at h
  rw [← high_gaussian_absolute_zero_mass K hne hx] at h
  have ha := high_gaussian_pole_ge_two K
  have hre (b t : ℝ) : ((b : ℂ) + Complex.I * (t : ℂ)).re = b := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
  have hl₁ (t : ℝ) : -(K.pole : ℝ) < (l t).re := by
    change _ < (((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)).re
    rw [hre]
    linarith only [ha]
  have hl₂ (t : ℝ) : (l t).re < (K.pole : ℝ) := by
    change (((-9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)).re < _
    rw [hre]
    linarith only [ha]
  have hr₁ (t : ℝ) : -(K.pole : ℝ) < (r t).re := by
    change _ < (((9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)).re
    rw [hre]
    linarith only [ha]
  have hr₂ (t : ℝ) : (r t).re < (K.pole : ℝ) := by
    change (((9 / 16 : ℝ) : ℂ) + Complex.I * (t : ℂ)).re < _
    rw [hre]
    linarith only [ha]
  have hl (t : ℝ) := mass_integrand K (hl₁ t) (hl₂ t) (-logDeriv χ.completedLFunction (l t + 1 / 2))
  have hr (t : ℝ) := mass_integrand K (hr₁ t) (hr₂ t) (logDeriv χ.gammaFactor (r t + 1 / 2))
  dsimp only [l, r] at hl hr
  simpa only [hl, hr, mass_arithmetic] using h

/-- The rational mass is even in the contour coordinate. -/
public theorem high_gaussian_mass_even (K : HighGaussianKernel) (z : ℂ) :
    K.massExtension (-z) = K.massExtension z := by
  simp only [HighGaussianKernel.massExtension, neg_sq]

/-- The signed mass profile is invariant under inversion of positive arguments. -/
public theorem high_gaussian_mass_profile_inv (K : HighGaussianKernel) {u : ℝ} (hu : 0 < u) :
    K.massProfile u⁻¹ = K.massProfile u := by
  rw [high_gaussian_mass_profile_log K (inv_pos.mpr hu), high_gaussian_mass_profile_log K hu,
    Real.log_inv, abs_neg]

/-- At a positive integer, the forward Mangoldt summand equals the
mass polynomial at the logarithm with the factor one half from Mellin inversion. -/
public theorem high_gaussian_mass_mangoldt_log (K : HighGaussianKernel) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : n ≠ 0) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n * (K.massProfile n : ℂ) =
      (((1 / 2 : ℝ) * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(K.pole : ℝ) - 1 / 2) *
              (highGaussianMassPolynomial K).eval₂ (Rat.castHom ℝ) (Real.log n) :
            ℝ) :
          ℂ) *
        χ n := by
  have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hn1 : 1 ≤ (n : ℝ) := by
    have h : ((1 : ℕ) : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr (Nat.one_le_iff_ne_zero.mpr hn)
    simpa only [Nat.cast_one] using h
  rw [high_gaussian_mass_profile_log K hn0, abs_of_nonneg (Real.log_nonneg hn1)]
  have he : Real.exp (-(K.pole : ℝ) * Real.log n) = (n : ℝ) ^ (-(K.pole : ℝ)) := by
    rw [Real.rpow_def_of_pos hn0, mul_comm (Real.log n)]
  rw [he, Real.sqrt_eq_rpow, sub_eq_add_neg, Real.rpow_add hn0]
  simp only [Real.rpow_neg hn0.le, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_inv]
  ring

/-- Reflection moves the left contour to the right contour for the even mass kernel. -/
public theorem high_gaussian_mass_reflect (K : HighGaussianKernel) (H : ℂ → ℂ) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    (∫ t : ℝ, H (-(l t)) * K.massExtension (l t)) = ∫ t : ℝ, H (r t) * K.massExtension (r t) := by
  intro l r
  let F := fun t ↦ H (r t) * K.massExtension (r t)
  have hr (t : ℝ) : r (-t) = -(l t) := by
    dsimp only [r, l]
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, mul_neg, neg_add_rev]
    ring
  have he (t : ℝ) : H (-(l t)) * K.massExtension (l t) = F (-t) := by
    simp only [F, hr, high_gaussian_mass_even]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall he)]
  exact MeasureTheory.integral_neg_eq_self F MeasureTheory.volume

/-- The constant log-conductor contribution on the left contour is exactly
the log conductor times the central profile value `3/16`. -/
public theorem high_gaussian_mass_conductor (K : HighGaussianKernel) (q : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, Complex.log (q : ℂ) * K.massExtension (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      Complex.log (q : ℂ) * ((3 / 16 : ℝ) : ℂ) := by
  have ha := high_gaussian_pole_ge_two K
  have h :=
    high_gaussian_mass_inversion K (c := -9 / 16) (by linarith only [ha]) (by linarith only [ha])
      zero_lt_one
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at h
  rw [MeasureTheory.integral_const_mul, mul_left_comm, h, high_gaussian_mass_profile_one]

/-- The ordinary logarithmic derivative on the right contour gives the unit-scale
Mangoldt series of the signed mass profile. -/
public theorem high_gaussian_mass_euler (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d * (∫ t : ℝ, -logDeriv χ.LFunction (r t + 1 / 2) * K.massExtension (r t)) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (K.massProfile n : ℂ) := by
  intro r d
  let B := fun j ↦ balancedPoleKernel K.pole (high_gaussian_pole_ge_two K) (K.degree + 1 - j)
  let c := fun j ↦ (K.normalization : ℂ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℂ)
  let G := fun j t ↦ -logDeriv χ.LFunction (r t + 1 / 2) * (B j).function (r t)
  have hb (j : ℕ) : (9 / 16 : ℝ) ≤ 1 / 2 + (B j).delta := by
    rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]
    norm_num only
  have hre (t : ℝ) : (r t).re = 9 / 16 := by
    simp only [r, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have ha := high_gaussian_pole_ge_two K
  have hm (t : ℝ) :
    (∑ j ∈ Finset.range (K.degree + 1), c j * G j t) =
      -logDeriv χ.LFunction (r t + 1 / 2) * K.massExtension (r t) :=
    mass_integrand K
      (by
        rw [hre]; linarith only [ha])
      (by
        rw [hre]; linarith only [ha])
      _
  have hi (j : ℕ) : MeasureTheory.Integrable (fun t ↦ c j * G j t) := by
    have h :=
      (B j).integrable_arithmeticMellin_logDeriv χ (x := 1) zero_lt_one
        (by norm_num only : (1 / 2 : ℝ) < 9 / 16) (hb j)
    simpa only [G, r, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  have hA (j : ℕ) : d * (∫ t : ℝ, G j t) = ∑' n : ℕ, (B j).summand χ 1 n := by
    have h :=
      (B j).tsum_summand_eq_integral_logDeriv χ (x := 1) zero_lt_one
        (by norm_num only : (1 / 2 : ℝ) < 9 / 16) (hb j)
    simpa only [G, r, d, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.symm
  simp_rw [← hm, MeasureTheory.integral_finsetSum _ (fun j _ ↦ hi j),
    MeasureTheory.integral_const_mul, Finset.mul_sum, mul_left_comm d, hA]
  rw [← LLS.PaperStatements.MellinKernel.tsum_kernel_finset_sum _ B c χ zero_lt_one]
  exact tsum_congr (mass_arithmetic K χ)

/-- Reflection converts the ordinary derivative on the left into the same
signed Mangoldt series as the right contour at unit scale. -/
public theorem high_gaussian_reflected_euler (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    d * (∫ t : ℝ, -logDeriv χ.LFunction (-(l t) + 1 / 2) * K.massExtension (l t)) =
      ∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
          (K.massProfile n : ℂ) := by
  intro l d
  have h := high_gaussian_mass_reflect K (fun z ↦ -logDeriv χ.LFunction (z + 1 / 2))
  dsimp only at h
  rw [h]
  exact high_gaussian_mass_euler K χ

end PseudoPrime.PrimeTestBounds.MillerRabin
