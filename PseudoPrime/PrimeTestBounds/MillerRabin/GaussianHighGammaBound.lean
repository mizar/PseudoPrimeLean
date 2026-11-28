/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExpansion
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaEndpointCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaExp

/-! # Upper bounds for the high Gaussian common contour -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Beyond the certified profile boundary the H33 contour is bounded by
upper gamma coefficients and the propagated convolution deficit. The
decaying moment adds zero for K186 and at most 806 for K196 before weighting. -/
theorem high_common_contour_tail_le (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {z NI : ℝ} (hz : (profileCorrectionEnd K : ℝ) ≤ z)
    (hI :
      max
          (-(∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ),
              Real.exp (((K.pole : ℝ) - 5 / 2) * ((profileCorrectionEnd K : ℝ) - t)) *
                K.realProfile.eval t))
          0 ≤
        NI)
    {u : ℕ → ℝ} (hu : ∀ j ∈ Finset.range (K.realProfile.natDegree + 1), highGammaCoeff K j ≤ u j) :
    let a := (K.pole : ℝ)
    let NJ : ℝ :=
      match K with
      | .k186 => 0
      | .k196 => 806
    highCommonContour K (Real.exp (z - 5)) ≤
      Real.exp (-a * z) *
          (∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
            u j * ((Polynomial.derivative^[j]) K.realProfile).eval z) +
        Real.exp (-a * z) * (Real.exp ((a - 5 / 2) * (z - (profileCorrectionEnd K : ℝ))) * NI) +
        Real.exp (-z / 2) * NJ := by
  intro a NJ
  have ha : 0 < (profileCorrectionEnd K : ℝ) := by
    cases K <;> norm_num only [profileCorrectionEnd, Int.cast_ofNat]
  have hJ :
    max
        (-(∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ),
            K.realProfile.eval t * Real.exp (-(a - 1 / 2) * t)))
        0 ≤
      NJ := by
    have h := high_gamma_decay_tail_cap K (z := (profileCorrectionEnd K : ℝ)) le_rfl
    cases K <;> exact h
  have hR := high_gamma_trivial_tail_nonneg K (a - 1 / 2) z
  rw [high_common_contour_h33 K hp hn hi he (ha.trans_le hz)]
  exact
    high_gamma_tail_expression_le K (C := Real.exp (-a * z)) (D := Real.exp (-z / 2)) hz hI hJ
      (Real.exp_pos _).le (Real.exp_pos _).le hR _ hu

/-- A rounded rational exponential enclosure and a separate shifted-moment
comparison establish nonnegativity without a large composite computation. -/
theorem high_gamma_conv_endpoint_nonneg (K : HighGaussianKernel) {a s E : ℚ} (ha : 0 ≤ a)
    (hs : 0 < s) (he : gammaConvExpUpper (s * a) 48 ≤ E)
    (hm : E * highGammaShiftMoment K a s ≤ highGammaRatTransform K s) :
    0 ≤ ∫ t in (0 : ℝ)..(a : ℝ), Real.exp ((s : ℝ) * ((a : ℝ) - t)) * K.realProfile.eval t := by
  have hE :=
    (gamma_conv_exp_upper_valid (mul_nonneg hs.le ha) (by norm_num only : 0 < 48)).trans
      (Rat.cast_le.mpr he)
  rw [Rat.cast_mul, ← neg_mul] at hE
  have hEn : 0 ≤ E := Rat.cast_nonneg.mp ((Real.exp_pos _).le.trans hE)
  have hT : 0 ≤ highGammaRatTransform K s := by
    apply (Rat.cast_nonneg (K := ℝ)).mp
    rw [high_gamma_transform_cast]
    exact high_profile_laplace_nonneg K _
  have hM : E * max 0 (highGammaShiftMoment K a s) ≤ highGammaRatTransform K s := by
    rw [mul_max_of_nonneg _ _ hEn, mul_zero]
    exact max_le hT hm
  apply high_gamma_conv_nonneg
  exact
    (Rat.cast_nonneg.mpr (sub_nonneg.mpr hM)).trans
      (high_gamma_endpoint_lower K ha hs (le_max_left _ _) (le_max_right _ _) hE)

end PseudoPrime.PrimeTestBounds.MillerRabin
