/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaWindow
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteContour
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaTailBound

/-! # The finite high cutoff with the Gamma offset absorbed -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the finite high window, the two Gamma convolution bounds and
the one signed coefficient row absorb the offset at a cost below 1/16. -/
theorem k186_finite_common_offset_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {z : ℝ}
    (hz : z ∈ Set.Icc (35 : ℝ) 65) :
    highCommonContour .k186 (Real.exp (z - 5)) +
        (4 / 3 : ℝ) * Real.exp (-(11 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z ≤
      1 / 16 := by
  have hc := k186_finite_common_le hp hn hi he hz
  have hg := k186_gamma_offset_ray_le hz.1
  simp only [highGammaOffset, mul_add] at hg
  linarith only [hc, hg]

/-- The same signed Gamma grid supplies the offset beyond height 65, where
the two convolution deficits are already zero. -/
private theorem k186_tail_common_offset_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) {z : ℝ} (hz : 65 ≤ z) :
    highCommonContour .k186 (Real.exp (z - 5)) +
        (4 / 3 : ℝ) * Real.exp (-(11 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z ≤
      1 / 16 := by
  have hEnd : (profileCorrectionEnd .k186 : ℝ) ≤ z := by
    simpa only [profileCorrectionEnd, Int.cast_ofNat] using hz
  have hI := max_le (neg_nonpos.mpr (high_gamma_conv_cutoff_nonneg .k186)) (le_refl (0 : ℝ))
  have hc :=
    high_common_contour_tail_le .k186 hp hn hi he hEnd hI
      (fun _ _ ↦ le_rfl : ∀ j ∈ _, highGammaCoeff .k186 j ≤ highGammaCoeff .k186 j)
  have hg := k186_gamma_offset_ray_le ((by norm_num only : (35 : ℝ) ≤ 65).trans hz)
  simp only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, mul_zero, add_zero] at hc
  simp only [highGammaOffset, mul_add] at hg
  linarith only [hc, hg]

/-- In the finite range the contour offset lowers the conductor
coefficient by four, with a constant budget for the three identical contours. -/
theorem k186_finite_base_loss_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (L : ℝ) {z : ℝ} (hz : 35 ≤ z) :
    k186DirectBaseLoss L (Real.exp (z - 5)) ≤
      (2 * L - 4) * Real.exp (-(11 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z +
            highReflectedBudget .k186 z -
          94173 / 1250 +
        3 * HighGaussianKernel.k186.xiMass.re +
        3 / 16 := by
  have h :
    highCommonContour .k186 (Real.exp (z - 5)) +
        (4 / 3 : ℝ) * Real.exp (-(11 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z ≤
      1 / 16 := by
    by_cases h65 : z ≤ 65
    · exact k186_finite_common_offset_le hp hn hi he ⟨hz, h65⟩
    · exact k186_tail_common_offset_le hp hn hi he (le_of_not_ge h65)
  have hz' : 5 + Real.log (Real.exp (z - 5)) = z := by
    rw [Real.log_exp]; ring
  unfold k186DirectBaseLoss
  simp only [hz', HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, sub_mul]
  linarith only [h]

/-- The finite scalar loss keeps the reflected term and right Euler tail
explicit after absorbing the common contour into the conductor coefficient. -/
noncomputable def k186FiniteLoss (L x : ℝ) : ℝ :=
  let z := 5 + x
  (2 * L - 4) * Real.exp (-(11 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z +
        highReflectedBudget .k186 z -
      94173 / 1250 +
    3 * HighGaussianKernel.k186.xiMass.re +
    3 / 16 +
    4 * k186TailCost (Real.exp x)

/-- At a positive cutoff with logarithm at least 30, an even primitive
quadratic character allows the direct loss to use the finite scalar budget. -/
theorem k186_direct_loss_le_finite {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (L : ℝ) {X : ℝ} (hX : 0 < X)
    (hx : 30 ≤ Real.log X) : k186DirectLoss L X ≤ k186FiniteLoss L (Real.log X) := by
  have hz : 35 ≤ 5 + Real.log X := by linarith only [hx]
  have h := k186_finite_base_loss_le hp hn hi he L hz
  rw [show 5 + Real.log X - 5 = Real.log X by ring, Real.exp_log hX] at h
  simpa only [k186DirectLoss, k186FiniteLoss, Real.exp_log hX] using
    add_le_add_left h (4 * k186TailCost X)

end PseudoPrime.PrimeTestBounds.MillerRabin
