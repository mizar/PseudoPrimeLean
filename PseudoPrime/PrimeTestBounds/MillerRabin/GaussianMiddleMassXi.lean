/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassContour
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassXi
import PseudoPrime.LLS.PaperStatements.MellinKernelZetaContourLimits

/-! # Xi contour identity for the middle Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Xi zero mass of the rational continuation, counted with multiplicity. -/
public noncomputable def middleXiMass (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) : ℂ :=
  ∑' ρ : AnalyticNumberTheory.RiemannXi.Zero,
    (AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity (ρ : ℂ) : ℂ) *
      middleMassExtension Q a (d + 2) (Complex.I * (ρ : ℂ).im)

/-- The two Xi contours give the absolute mass of the middle kernel at the zeta zeros. -/
public theorem middle_xi_mass_contours (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) (hRH : RiemannHypothesis) :
    let F := fun z : ℂ ↦
      -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (z + 1 / 2) *
        middleMassExtension Q a (d + 2) z
    middleXiMass Q a d =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, F (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, F (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  intro F
  let s := Finset.range (d + 1)
  let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  let G := fun j z ↦
    -logDeriv (AnalyticNumberTheory.RiemannXi.riemannXi) (z + 1 / 2) * (B j).function z
  have H (z : ℂ) (hl : -(a : ℝ) < z.re) (hr : z.re < (a : ℝ)) : F z = ∑ j ∈ s, c j * G j z := by
    dsimp only [F]
    rw [middle_mass_balanced_sum Q a ha hd hQ hl hr, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
  have HE (b t : ℝ) : ((b : ℂ) + Complex.I * (t : ℂ)).re = b := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
  have HP (b : ℝ) (hb₁ : -1 ≤ b) (hb₂ : b ≤ 1) (t : ℝ) :
    F ((b : ℂ) + Complex.I * (t : ℂ)) = ∑ j ∈ s, c j * G j ((b : ℂ) + Complex.I * (t : ℂ)) :=
    H _
      (by
        rw [HE]; linarith only [ha, hb₁])
      (by
        rw [HE]; linarith only [ha, hb₂])
  have hb (j : ℕ) : (B j).delta = 1 / 8 := balanced_pole_delta _ _ _
  have hL (j : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ c j * G j (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    have h :=
      (B j).integrable_xi_left_line (x := 1) (c := -9 / 16)
        (by
          rw [hb]; norm_num only)
        (by norm_num only) (by norm_num only) zero_lt_one
    simpa only [G, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  have hR (j : ℕ) :
    MeasureTheory.Integrable (fun t : ℝ ↦ c j * G j (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    have h :=
      (B j).integrable_xi_right_line (x := 1) (c := 9 / 16) (by norm_num only)
        (by
          rw [hb]; norm_num only)
        (by norm_num only) zero_lt_one
    simpa only [G, Complex.ofReal_one, Complex.one_cpow, mul_one] using h.const_mul (c j)
  simp_rw [HP (-9 / 16) (by norm_num only) (by norm_num only),
    HP (9 / 16) (by norm_num only) (by norm_num only)]
  rw [MeasureTheory.integral_finsetSum s (fun j _ ↦ hL j),
    MeasureTheory.integral_finsetSum s (fun j _ ↦ hR j)]
  simp only [MeasureTheory.integral_const_mul, ← Finset.sum_sub_distrib, Finset.mul_sum, ← mul_sub,
    mul_left_comm (((1 / (2 * Real.pi) : ℝ) : ℂ))]
  have hh (j : ℕ) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((∫ t : ℝ, G j (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) -
          ∫ t : ℝ, G j (((9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      ∑' ρ, (B j).zetaOscillatingZeroTerm 1 ρ :=
    (balanced_xi_contour ha (d + 1 - j) hRH).symm
  have hc (j : ℕ) :
    c j * (∑' ρ, (B j).zetaOscillatingZeroTerm 1 ρ) =
      ∑' ρ, c j * (B j).zetaOscillatingZeroTerm 1 ρ :=
    (((B j).summable_zetaOscillatingZeroTerm hRH zero_lt_one).tsum_mul_left (c j)).symm
  simp only [hh, hc]
  rw [←
    Summable.tsum_finsetSum
      (fun j _ ↦ ((B j).summable_zetaOscillatingZeroTerm hRH zero_lt_one).mul_left (c j))]
  unfold middleXiMass
  apply tsum_congr
  intro ρ
  have hre : (Complex.I * ((ρ : ℂ).im : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [middle_mass_balanced_sum Q a ha hd hQ (z := Complex.I * (ρ : ℂ).im)
      (by
        rw [hre]; linarith only [ha])
      (by
        rw [hre]; linarith only [ha]),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LLS.PaperStatements.MellinKernel.zetaOscillatingZeroTerm,
    LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, Complex.ofReal_one, Complex.one_cpow,
    mul_one]
  rw [mul_left_comm]

end PseudoPrime.PrimeTestBounds.MillerRabin
