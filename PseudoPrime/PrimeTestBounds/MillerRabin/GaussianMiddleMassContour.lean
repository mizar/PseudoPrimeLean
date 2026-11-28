/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassExtension
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassExtension
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianBalancedPoleKernel
import PseudoPrime.LLS.PaperStatements.MellinKernelSignedFormula

/-! # Unit-scale contour formula for the middle Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The middle mass is a signed combination of admissible balanced Mellin kernels. -/
public theorem middle_mass_balanced_sum (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) {z : ℂ} (hl : -(a : ℝ) < z.re) (hr : z.re < (a : ℝ)) :
    middleMassExtension Q a (d + 2) z =
      ∑ j ∈ Finset.range (d + 1),
        ((normSqPolynomial a Q).coeff j : ℂ) *
          (balancedPoleKernel a ha (d + 1 - j)).function z := by
  rw [middle_mass_extension_sum Q a hd hQ hl hr]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : d + 1 - j + 1 = d + 2 - j := (Nat.sub_add_comm (hj'.trans (Nat.le_succ d))).symm
  rw [balanced_pole_function, hm, ← mul_pow]
  have hprod : ((a : ℂ) + z) * ((a : ℂ) - z) = (a : ℂ) ^ 2 - z ^ 2 := by ring
  simp only [Complex.ofReal_ratCast, hprod, mul_one_div]

/-- At unit scale the balanced zero weights give the continued middle mass
times the exact zero multiplicity. -/
public theorem middle_mass_zero_weight (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ) :
    let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
    let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
    (∑ j ∈ Finset.range (d + 1), c j * (B j).oscillatingZeroTerm χ 1 ρ) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) *
        middleMassExtension Q a (d + 2) (Complex.I * (ρ.im : ℂ)) := by
  intro B c
  have ha₀ := (by norm_num only : (0 : ℝ) < 2).trans_le ha
  have hre : (Complex.I * (ρ.im : ℂ)).re = 0 := by
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  rw [middle_mass_balanced_sum Q a ha hd hQ (z := Complex.I * (ρ.im : ℂ))
      (by
        rw [hre]; exact neg_lt_zero.mpr ha₀)
      (by
        rw [hre]; exact ha₀),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [LLS.PaperStatements.MellinKernel.oscillatingZeroTerm,
    LLS.PaperStatements.MellinKernel.kernelZeroTerm, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [mul_left_comm]

/-- The middle Gaussian zero mass satisfies the signed contour formula
obtained by summing the admissible balanced pole components at unit scale. -/
public theorem middle_mass_zero_contours (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ))
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
    let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
    let s := Finset.range (d + 1)
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let d := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    (∑' ρ : ℂ, ∑ j ∈ s, c j * (B j).oscillatingZeroTerm χ 1 ρ) =
      d *
            (∫ t : ℝ,
              ∑ j ∈ s,
                c j * (-logDeriv χ.completedLFunction (l t + 1 / 2) * (B j).function (l t))) +
          d *
            (∫ t : ℝ,
              ∑ j ∈ s, c j * (logDeriv χ.gammaFactor (r t + 1 / 2) * (B j).function (r t))) -
        (∑' n : ℕ, ∑ j ∈ s, c j * (B j).summand χ 1 n) := by
  intro B c s l r d
  have h :=
    LLS.PaperStatements.MellinKernel.tsum_signed_kernel_contours s B c hq hg hp hne
      (inv_ne_one.mpr hne) (a := (-9 / 16 : ℝ)) (b := 9 / 16) (x := 1) (by norm_num only)
      (fun j _ ↦ by
        rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (fun j _ ↦ by
        rw [show (B j).delta = 1 / 8 from balanced_pole_delta _ _ _]; norm_num only)
      (by norm_num only) (by norm_num only) le_rfl (by norm_num only) (by norm_num only)
  have hz (j : ℕ) (F : ℂ → ℂ) : (B j).weightedResidue F 1 (-1 / 2) = 0 := by
    simp only [LLS.PaperStatements.MellinKernel.weightedResidue, ite_true]
    change -logDeriv F (-1 / 2) * (((-1 / 2 : ℂ) + 1 / 2) * _ * _) = 0
    rw [neg_div, neg_add_cancel, zero_mul, zero_mul, mul_zero]
  dsimp only at h
  simp only [hz, Complex.ofReal_one, Complex.one_cpow, mul_one, mul_zero, Finset.sum_const_zero,
    zero_sub] at h
  linear_combination h

private theorem middle_mass_mangoldt (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (ha : 2 ≤ (a : ℝ)) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ) :
    (∑ j ∈ Finset.range (d + 1),
        ((normSqPolynomial a Q).coeff j : ℂ) *
          (balancedPoleKernel a ha (d + 1 - j)).summand χ 1 n) =
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
        (middleMassProfile Q a d n : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp only [LLS.PaperStatements.MellinKernel.summand, ite_true, mul_zero, Finset.sum_const_zero,
      Nat.cast_zero, Real.sqrt_zero, div_zero, Complex.ofReal_zero, zero_mul]
  have hu : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hl : -(a : ℝ) < 0 := by linarith only [ha]
  have hr : 0 < (a : ℝ) := by linarith only [ha]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn, div_one,
    LLS.PaperStatements.MellinKernel.transform, balanced_pole_inverse ha _ hl hr hu,
    middleMassProfile, Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hm : d + 1 - j + 1 = d + 2 - j := (Nat.sub_add_comm (hj'.trans (Nat.le_succ d))).symm
  rw [hm]
  simp only [Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ratCast, div_eq_mul_inv]
  ring

/-- The zero mass of the middle extension is the difference of its contour
and Mangoldt expressions. The two contour integrands use the combined kernel. -/
public theorem middle_mass_contour_identity (Q : Polynomial ℚ) (a : ℚ) {d : ℕ} (ha : 2 ≤ (a : ℝ))
    (hd : 1 ≤ d) (hQ : Q.natDegree ≤ d) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hg : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    let l := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let F := middleMassExtension Q a (d + 2)
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℂ) * F (Complex.I * ρ.im)) =
      D * (∫ t : ℝ, -logDeriv χ.completedLFunction (l t + 1 / 2) * F (l t)) +
          D * (∫ t : ℝ, logDeriv χ.gammaFactor (r t + 1 / 2) * F (r t)) -
        (∑' n : ℕ,
          ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) * χ n *
            (middleMassProfile Q a d n : ℂ)) := by
  intro l r D F
  let B := fun j ↦ balancedPoleKernel a ha (d + 1 - j)
  let c := fun j ↦ ((normSqPolynomial a Q).coeff j : ℂ)
  have h := middle_mass_zero_contours Q a d ha hq hg hp hne
  have hre (σ t : ℝ) : ((σ : ℂ) + Complex.I * t).re = σ := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
  have hl (t : ℝ) : |(l t).re| ≤ 1 := by
    norm_num only [l, hre, abs_of_nonpos (by norm_num only : (-9 / 16 : ℝ) ≤ 0)]
  have hr (t : ℝ) : |(r t).re| ≤ 1 := by
    norm_num only [r, hre, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 9 / 16)]
  have hsum (g z : ℂ) (hz : |z.re| ≤ 1) :
    (∑ j ∈ Finset.range (d + 1), c j * (g * (B j).function z)) = g * F z := by
    have hz' := abs_le.mp hz
    rw [show F z = _ from
        middle_mass_balanced_sum Q a ha hd hQ (by linarith only [ha, hz'.1])
          (by linarith only [ha, hz'.2]),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ mul_left_comm _ _ _
  change
    (∑' ρ : ℂ, ∑ j ∈ Finset.range (d + 1), c j * (B j).oscillatingZeroTerm χ 1 ρ) =
      D *
            (∫ t : ℝ,
              ∑ j ∈ Finset.range (d + 1),
                c j * (-logDeriv χ.completedLFunction (l t + 1 / 2) * (B j).function (l t))) +
          D *
            (∫ t : ℝ,
              ∑ j ∈ Finset.range (d + 1),
                c j * (logDeriv χ.gammaFactor (r t + 1 / 2) * (B j).function (r t))) -
        _ at h
  simp only [hsum _ _ (hl _), hsum _ _ (hr _), middle_mass_mangoldt Q a d ha χ] at h
  exact (tsum_congr fun ρ ↦ (middle_mass_zero_weight Q a ha hd hQ χ ρ).symm).trans h

end PseudoPrime.PrimeTestBounds.MillerRabin
