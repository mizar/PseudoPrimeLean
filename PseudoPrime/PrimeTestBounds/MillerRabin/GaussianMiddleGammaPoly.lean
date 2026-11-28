/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaMajorant
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141GammaWidth
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaWidth
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156GammaNet

/-! # Uniform middle Gamma derivative-sum bounds -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On the full physical height range of K141, one rational upper
polynomial and one millionth bound the scaled Gamma derivative sum. -/
public theorem middle_k141_gamma_poly_le {z : ℝ} (hz : 47 / 2 ≤ z) (hz' : z ≤ 57 / 2) :
    let W := (middleK141Norm : ℝ) * Real.exp (-(2 : ℝ) * z)
    let P := middleK141Profile
    let R := P.map (Rat.castHom ℝ)
    W *
        (∑ j ∈ Finset.range (R.natDegree + 1),
          middleGammaDerivCoeff (2 : ℚ) true j * ((Polynomial.derivative^[j]) R).eval z) ≤
      W * ((middleGammaUpperPoly P middleK141GammaRow).map (Rat.castHom ℝ)).eval z +
        1 / 10 ^ 6 := by
  intro W P R
  have hW : 0 ≤ W := mul_nonneg (Rat.cast_nonneg.mpr (by decide +kernel)) (Real.exp_pos _).le
  have hd : R.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) Rat.cast_injective _
  rw [hd]
  have hcell (c w : ℚ) (hc : |z - (c : ℝ)| ≤ (w : ℝ))
    (hcap : W * (middleGammaWidthBudget P c w middleK141GammaRow : ℝ) ≤ 1 / 10 ^ 6) : _ :=
    middle_gamma_scaled_poly_le P middleK141GammaRow _ hc hW
      (fun j _ ↦ middle_k141_gamma_row_sound j) hcap
  by_cases h0 : z ≤ 26
  · refine hcell (99 / 4) (5 / 4) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hz, h0]
    · exact middle_k141_gamma_scaled0 hz
  have hl1 : 26 ≤ z := (lt_of_not_ge h0).le
  refine hcell (109 / 4) (5 / 4) ?_ ?_
  · rw [abs_le]
    constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl1, hz']
  · exact middle_k141_gamma_scaled1 hl1

/-- On the full physical height range of K156, one rational upper
polynomial and one millionth bound the scaled Gamma derivative sum. -/
public theorem middle_k156_gamma_poly_le {z : ℝ} (hz : 55 / 2 ≤ z) (hz' : z ≤ 135 / 4) :
    let W := (middleK156Norm : ℝ) * Real.exp (-(49 / 20 : ℝ) * z)
    let P := middleK156Profile
    let R := P.map (Rat.castHom ℝ)
    W *
        (∑ j ∈ Finset.range (R.natDegree + 1),
          middleGammaDerivCoeff (49 / 20 : ℚ) false j * ((Polynomial.derivative^[j]) R).eval z) ≤
      W * ((middleGammaUpperPoly P middleK156GammaRow).map (Rat.castHom ℝ)).eval z +
        1 / 10 ^ 6 := by
  intro W P R
  have hW : 0 ≤ W := mul_nonneg (Rat.cast_nonneg.mpr (by decide +kernel)) (Real.exp_pos _).le
  have hd : R.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) Rat.cast_injective _
  rw [hd]
  have hcell (c w : ℚ) (hc : |z - (c : ℝ)| ≤ (w : ℝ))
    (hcap : W * (middleGammaWidthBudget P c w middleK156GammaRow : ℝ) ≤ 1 / 10 ^ 6) : _ :=
    middle_gamma_scaled_poly_le P middleK156GammaRow _ hc hW
      (fun j _ ↦ middle_k156_gamma_row_sound j) hcap
  by_cases h0 : z ≤ 57 / 2
  · refine hcell (28) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hz, h0]
    · simpa only [div_one] using middle_k156_gamma_scaled0 hz
  have hl1 : 57 / 2 ≤ z := (lt_of_not_ge h0).le
  by_cases h1 : z ≤ 59 / 2
  · refine hcell (29) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl1, h1]
    · simpa only [div_one] using middle_k156_gamma_scaled1 hl1
  have hl2 : 59 / 2 ≤ z := (lt_of_not_ge h1).le
  by_cases h2 : z ≤ 61 / 2
  · refine hcell (30) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl2, h2]
    · simpa only [div_one] using middle_k156_gamma_scaled2 hl2
  have hl3 : 61 / 2 ≤ z := (lt_of_not_ge h2).le
  by_cases h3 : z ≤ 63 / 2
  · refine hcell (31) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl3, h3]
    · simpa only [div_one] using middle_k156_gamma_scaled3 hl3
  have hl4 : 63 / 2 ≤ z := (lt_of_not_ge h3).le
  by_cases h4 : z ≤ 65 / 2
  · refine hcell (32) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl4, h4]
    · simpa only [div_one] using middle_k156_gamma_scaled4 hl4
  have hl5 : 65 / 2 ≤ z := (lt_of_not_ge h4).le
  by_cases h5 : z ≤ 67 / 2
  · refine hcell (33) (1 / 2) ?_ ?_
    · rw [abs_le]
      constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl5, h5]
    · simpa only [div_one] using middle_k156_gamma_scaled5 hl5
  have hl6 : 67 / 2 ≤ z := (lt_of_not_ge h5).le
  refine hcell (269 / 8) (1 / 8) ?_ ?_
  · rw [abs_le]
    constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat] <;> linarith only [hl6, hz']
  · exact middle_k156_gamma_scaled6 hl6

/-- The full K141 Gamma contour bound uses one rational upper polynomial
and the certified physical allowance on its middle interval. -/
public theorem middle_k141_gamma_upper_le {x : ℝ} (hx : 20 ≤ x) (hx' : x ≤ 25) :
    let a : ℝ := 2
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 32,
        ((middleK141Kernel ^ 2).coeff (31 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let z := b + x
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let κ := (middleK141Norm : ℝ)
    κ *
        ((D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
          (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re) ≤
      κ * Real.exp (-a * z) *
            ((middleGammaUpperPoly middleK141Profile middleK141GammaRow).map (Rat.castHom ℝ)).eval
              z -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 32) -
          κ *
            (Real.exp (-(5 / 2) * z) * (middleK141Kernel.eval₂ (Rat.castHom ℝ) (-(1 / 2))) ^ 2 /
              (-(1 / 2) : ℝ) ^ 32) +
        1 / 10 ^ 6 := by
  intro a b ha r l F W z D κ
  have hz₀ : 47 / 2 ≤ z := by
    dsimp only [z, b]; linarith only [hx]
  have hz₁ : z ≤ 57 / 2 := by
    dsimp only [z, b]; linarith only [hx']
  have hmain := middle_k141_gamma_contour_le hx
  have hpoly := middle_k141_gamma_poly_le hz₀ hz₁
  dsimp only [r, l, F, W, z, D, κ, a, b] at hmain hpoly ⊢
  linear_combination hmain + hpoly

/-- The full K156 Gamma contour bound uses one rational upper polynomial
and the certified physical allowance on its middle interval. -/
public theorem middle_k156_gamma_upper_le {x : ℝ} (hx : 24 ≤ x) (hx' : x ≤ 121 / 4) :
    let a : ℝ := 49 / 20
    let b : ℝ := 7 / 2
    let ha : 1 / 2 < a := by norm_num only [a]
    let r := fun t : ℝ ↦ ((9 / 16 : ℝ) : ℂ) + Complex.I * t
    let l := fun t : ℝ ↦ ((-(9 / 16) : ℝ) : ℂ) + Complex.I * t
    let F := fun s ↦
      ∑ i ∈ Finset.Ico 3 52,
        ((middleK156Kernel ^ 2).coeff (51 - i) : ℂ) *
          (LLS.PaperStatements.shiftedPoleKernel (max 1 i) a b (le_max_left _ _) ha).function s
    let W := fun s : ℂ ↦ F s * Complex.exp (s * (x : ℂ))
    let z := b + x
    let D := ((1 / (2 * Real.pi) : ℝ) : ℂ)
    let κ := (middleK156Norm : ℝ)
    κ *
        ((D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (r t + 1 / 2) * W (r t))).re +
          (D * (∫ t : ℝ, logDeriv Complex.Gammaℝ (1 / 2 - l t) * W (l t))).re) ≤
      κ * Real.exp (-a * z) * (middleK156GammaNet.map (Rat.castHom ℝ)).eval z -
          κ *
            (Real.exp (-(1 / 2) * z) * (middleK156Kernel.eval₂ (Rat.castHom ℝ) (a - 1 / 2)) ^ 2 /
              (a - 1 / 2) ^ 52) +
        2 / 10 ^ 6 := by
  intro a b ha r l F W z D κ
  have hz₀ : 55 / 2 ≤ z := by
    dsimp only [z, b]; linarith only [hx]
  have hz₁ : z ≤ 135 / 4 := by
    dsimp only [z, b]; linarith only [hx']
  have hmain := middle_k156_gamma_contour_le hx hx'
  have hpoly := middle_k156_gamma_poly_le hz₀ hz₁
  rw [middle_k156_gamma_net_eval]
  dsimp only [r, l, F, W, z, D, κ, a, b] at hmain hpoly ⊢
  linear_combination hmain + hpoly

end PseudoPrime.PrimeTestBounds.MillerRabin
