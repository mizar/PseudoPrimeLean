/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCoefficients
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaConvCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness

/-! # Certified high Gaussian contour bounds beyond the moment cutoffs -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At the H37 boundary, the two convolution endpoint certificates
eliminate the positive convolution correction for either high kernel. -/
theorem high_gamma_conv_cutoff_nonneg (K : HighGaussianKernel) :
    0 ≤
      ∫ t in (0 : ℝ)..(profileCorrectionEnd K : ℝ),
        Real.exp (((K.pole : ℝ) - 5 / 2) * ((profileCorrectionEnd K : ℝ) - t)) *
          K.realProfile.eval t := by
  cases K
  · have h186 :=
      high_gamma_conv_endpoint_nonneg .k186 (by norm_num only) (by norm_num only)
        k186_conv_exp_check k186_conv_moment_check
    norm_num only [profileCorrectionEnd, Int.cast_ofNat, HighGaussianKernel.pole, Rat.cast_div,
      Rat.cast_ofNat] at h186 ⊢
    exact h186
  · have h196 :=
      high_gamma_conv_endpoint_nonneg .k196 (by norm_num only) (by norm_num only)
        k196_conv_exp_check k196_conv_moment_check
    norm_num only [profileCorrectionEnd, Int.cast_ofNat, HighGaussianKernel.pole, Rat.cast_div,
      Rat.cast_ofNat] at h196 ⊢
    exact h196

/-- The real H34 upper polynomial evaluated with a supplied gamma enclosure. -/
noncomputable def highGammaOffset (K : HighGaussianKernel) (u : ℕ → ℝ) (z : ℝ) : ℝ :=
  (4 / 3 : ℝ) * K.realProfile.eval z +
    ∑ j ∈ Finset.range (K.realProfile.natDegree + 1),
      u j * ((Polynomial.derivative^[j]) K.realProfile).eval z

/-- A nonpositive H34 upper polynomial absorbs the four-thirds profile
offset. The common contour then leaves only the decaying-moment charge. -/
theorem high_common_contour_offset_le (K : HighGaussianKernel) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even)
    {z : ℝ} (hz : (profileCorrectionEnd K : ℝ) ≤ z) {u : ℕ → ℝ}
    (hu : ∀ j ∈ Finset.range (K.realProfile.natDegree + 1), highGammaCoeff K j ≤ u j)
    (hP : highGammaOffset K u z ≤ 0) :
    let a := (K.pole : ℝ)
    let NJ : ℝ :=
      match K with
      | .k186 => 0
      | .k196 => 806
    highCommonContour K (Real.exp (z - 5)) +
        (4 / 3 : ℝ) * Real.exp (-a * z) * K.realProfile.eval z ≤
      Real.exp (-z / 2) * NJ := by
  intro a NJ
  have hI := max_le (neg_nonpos.mpr (high_gamma_conv_cutoff_nonneg K)) (le_refl (0 : ℝ))
  have h := high_common_contour_tail_le K hp hn hi he hz hI hu
  simp only [highGammaOffset] at hP
  simp only [mul_zero, add_zero] at h
  have heP := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-a * z)).le hP
  dsimp only [a, NJ] at *
  cases K <;> linarith only [h, heP]

/-- Combine the common-contour offset with the conductor term. -/
private theorem high_score_offset_arith {A S L E P R C D J : ℝ}
    (hc : A ≤ S + 2 * L * E * P + R + 3 * C) (h : C + (4 / 3 : ℝ) * E * P ≤ D * J) :
    A ≤ S + (2 * L - 4) * E * P + R + 3 * D * J := by
  simp only [sub_mul]
  linarith only [hc, h]

/-- For a passing uniform triple, a nonpositive H34 upper polynomial reduces
the conductor coefficient by four and leaves only the decaying contour charge. -/
theorem gaussian_high_zero_score_offset
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (K : HighGaussianKernel)
    {n p q r : ℕ} [NeZero p] [NeZero q] [NeZero r] [NeZero n] [Fact p.Prime] [Fact q.Prime]
    [Fact r.Prime] [Fact (2 < p)] [Fact (2 < q)] [Fact (2 < r)] (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hprod : n = p * q * r) (hp : Odd p) (hq : Odd q) (hr : Odd r)
    {X : ℝ} (hX : 1000000 ≤ X) (hz : (profileCorrectionEnd K : ℝ) ≤ 5 + Real.log X) {u : ℕ → ℝ}
    (hγ : ∀ j ∈ Finset.range (K.realProfile.natDegree + 1), highGammaCoeff K j ≤ u j)
    (hP : highGammaOffset K u (5 + Real.log X) ≤ 0)
    (hpass : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → PrimeTest.StrongMillerRabinPass n (l : ZMod n)) :
    let z := 5 + Real.log X
    let v := fun m : ℕ ↦ 5 - Real.log ((m : ℝ) / X)
    let B := fun m : ℕ ↦
      ArithmeticFunction.vonMangoldt m * (m : ℝ) ^ (-(1 / 2) : ℝ) * Real.exp (-(K.pole : ℝ) * v m) *
        K.realProfile.eval (v m)
    4 * (∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, B m) - (∑ m ∈ Finset.Ioc 0 ⌊X * Real.exp 5⌋₊, B m) -
        4 * highCompensationBound K X ≤
      gaussianPairZeroScore K X hp hq hr +
        (2 * Real.log n - 4) * Real.exp (-(K.pole : ℝ) * z) * K.realProfile.eval z +
        highReflectedBudget K z +
        3 * Real.exp (-z / 2) *
          (match K with
          | .k186 => 0
          | .k196 => 806) := by
  intro z v B
  have h₁ := (by norm_num only : (1 : ℝ) ≤ 1000000).trans hX
  have hs : (profileCorrectionStart K : ℝ) ≤ (profileCorrectionEnd K : ℝ) := by
    cases K <;>
      norm_num only [profileCorrectionStart, profileCorrectionEnd, Int.cast_ofNat, Rat.cast_ofNat,
        Rat.cast_div]
  have hc := gaussian_high_zero_score_costs hGRH K hn ho hu hprod hp hq hr hX (hs.trans hz) hpass
  obtain ⟨_, _, _, ha, _, _, _⟩ := pair_data_of_uniform_pass hn ho hu hprod hp hq hr X hpass
  have h := high_common_contour_offset_le K ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hz hγ hP
  dsimp only at hc h
  rw [show 5 + Real.log X - 5 = Real.log X by ring, Real.exp_log (zero_lt_one.trans_le h₁)] at h
  dsimp only [z, v, B]
  cases K <;> exact high_score_offset_arith hc h

end PseudoPrime.PrimeTestBounds.MillerRabin
