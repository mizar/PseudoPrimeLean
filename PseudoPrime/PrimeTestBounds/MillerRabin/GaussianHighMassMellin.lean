/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassPole
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Mellin profile for the high Gaussian absolute mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Signed Mellin profile of the rational absolute mass. The factor one half
accounts for the two equal terms in the balanced opposite-pole transform. -/
public noncomputable def HighGaussianKernel.massProfile (K : HighGaussianKernel) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (K.degree + 1),
    (K.normalization : ℝ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℝ) / 2 *
      k131SymmetricProfile K.pole (K.degree + 2 - j) (K.degree + 2 - j) u

/-- The normalized balanced profile contributes a single opposite-pole product. -/
private theorem balanced_mellin {a : ℝ} {z : ℂ} (hl : -a < z.re) (hr : z.re < a) (m : ℕ)
    (hm : 0 < m) (c : ℝ) :
    HasMellin (fun u ↦ ((c / 2 * k131SymmetricProfile a m m u : ℝ) : ℂ)) z
      ((c : ℂ) / (((a : ℂ) + z) ^ m * ((a : ℂ) - z) ^ m)) := by
  have h := k131_symmetric_profile_mellin hl hr m m (Nat.add_pos_left hm _)
  have h' := hasMellin_const_smul h.1 (((c / 2 : ℝ) : ℂ))
  rw [h.2] at h'
  have he :
    ((c / 2 : ℝ) : ℂ) •
        (1 / (((a : ℂ) + z) ^ m * ((a : ℂ) - z) ^ m) +
          1 / (((a : ℂ) + z) ^ m * ((a : ℂ) - z) ^ m)) =
      (c : ℂ) / (((a : ℂ) + z) ^ m * ((a : ℂ) - z) ^ m) := by
    simp only [smul_eq_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
    simp only [div_eq_mul_inv]
    ring
  rw [he] at h'
  simpa only [smul_eq_mul, Complex.ofReal_mul] using h'

/-- On the open strip bounded by its two poles, the rational continuation is
the Mellin transform of the signed mass profile. -/
public theorem high_gaussian_mass_hasMellin (K : HighGaussianKernel) {z : ℂ}
    (hl : -(K.pole : ℝ) < z.re) (hr : z.re < (K.pole : ℝ)) :
    HasMellin (fun u ↦ (K.massProfile u : ℂ)) z (K.massExtension z) := by
  rw [high_gaussian_mass_extension_sum K hl hr]
  unfold HighGaussianKernel.massProfile
  simp only [Complex.ofReal_sum]
  apply k131_mellin_finsum
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : 0 < K.degree + 2 - j :=
    Nat.sub_pos_of_lt (hj'.trans_lt (Nat.lt_add_of_pos_right (by decide : 0 < 2)))
  simpa only [Complex.ofReal_mul, Complex.ofReal_ratCast] using
    balanced_mellin hl hr (K.degree + 2 - j) hm
      ((K.normalization : ℝ) * ((normSqPolynomial K.pole K.polynomial).coeff j : ℝ))

/-- The signed mass profile is continuous at every positive argument,
as required by pointwise Mellin inversion. -/
public theorem high_gaussian_mass_profile_cont (K : HighGaussianKernel) {u : ℝ} (hu : 0 < u) :
    ContinuousAt K.massProfile u := by
  unfold HighGaussianKernel.massProfile
  classical
  generalize Finset.range (K.degree + 1) = s
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact continuousAt_const
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact ((k131_symmetric_cont hu _ _ _).const_mul _).add ih

/-- The Mellin moment at the principal pole is exactly the certified rational value. -/
public theorem high_gaussian_mass_profile_half (K : HighGaussianKernel) :
    HasMellin (fun u ↦ (K.massProfile u : ℂ)) (1 / 2) (K.massPole : ℂ) := by
  have hk := high_gaussian_pole_gt K
  have hre : ((1 / 2 : ℂ)).re = 1 / 2 := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      Complex.ofReal_re (1 / 2 : ℝ)
  have hl : -(K.pole : ℝ) < ((1 / 2 : ℂ)).re := by
    rw [hre]
    linarith only [hk]
  rw [← high_gaussian_mass_extension_half]
  exact high_gaussian_mass_hasMellin K hl (hre ▸ hk)

end PseudoPrime.PrimeTestBounds.MillerRabin
