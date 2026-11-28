/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalTail
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalMoments
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalMoments
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadNumeric
import Mathlib.Tactic.Ring

/-! # Centered moment bound for the high Gaussian principal tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered polynomial combines the endpoint and the reflected derivative. -/
@[expose]
public noncomputable def highCenteredProfile (K : HighGaussianKernel) : Polynomial ℝ :=
  Polynomial.C ((K.pole : ℝ) - 1 / 2) * K.realProfile - K.realProfile.derivative

/-- The absolute inverse-power sum for the centered polynomial at height 100. -/
@[expose]
public noncomputable def highCenteredMass (K : HighGaussianKernel) : ℝ :=
  let P := highCenteredProfile K
  ∑ j ∈ Finset.range (P.natDegree + 1), |principalMomentCoeff P 5 j| * (j.factorial : ℝ) / 100 ^ j

/-- The centered prefactor above height 100 includes the compact square just once. -/
@[expose]
public noncomputable def highCenteredTail (K : HighGaussianKernel) : ℝ :=
  (K.normalization : ℝ) * highCompactMass K ^ 2 / 100 ^ 2 +
    4 * Real.exp (-(5 * (K.pole : ℝ))) * highCenteredMass K

/-- Translating a purely imaginary height by a real number does not decrease its norm. -/
private theorem height_le_shift_norm (a t : ℝ) : t ≤ ‖(a : ℂ) + Complex.I * (t : ℂ)‖ := by
  have h := Complex.abs_im_le_norm ((a : ℂ) + Complex.I * (t : ℂ))
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add] at h
  exact (le_abs_self t).trans h

/-- The grouped coefficients give an inverse-square bound at each height above 100. -/
public theorem high_centered_tail_le (K : HighGaussianKernel) {t : ℝ} (ht : 100 < t) :
    ‖highPrincipalMultiplier K t‖ ≤ highCenteredTail K / t ^ 2 := by
  have ht0 := (by norm_num only : (0 : ℝ) < 100).trans ht
  have h₂ : (100 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num only) ht.le 2
  have hn : 0 ≤ (K.normalization : ℝ) := Rat.cast_nonneg.mpr (high_gaussian_normalization_pos K).le
  have hN := mul_nonneg hn (sq_nonneg (highCompactMass K))
  have hs : t ≤ ‖Complex.I * (t : ℂ) + (K.pole : ℂ)‖ := by
    rw [add_comm, ← Complex.ofReal_ratCast]
    exact height_le_shift_norm _ _
  have hr : t ≤ ‖(1 / 2 : ℂ) + Complex.I * (t : ℂ)‖ := by
    have he : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by
      simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
    rw [← he]
    exact height_le_shift_norm _ _
  have hm :=
    principal_moment_tail_le (highCenteredProfile K) 5 100 t _ _ (by norm_num only) ht.le hs hr
  have he : ‖Complex.exp (-(5 * (K.pole : ℂ)))‖ = Real.exp (-(5 * (K.pole : ℝ))) := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_ofNat (n := 5), ← Complex.ofReal_mul, ←
      Complex.ofReal_neg, Complex.norm_exp, Complex.ofReal_re]
  rw [high_principal_multiplier_centered]
  unfold highCenteredTail
  rw [add_div]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (high_square_tail_le K ht0).trans ?_
    rw [show t ^ 4 = t ^ 2 * t ^ 2 by ring, ← div_div]
    exact
      div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hN (by norm_num only) h₂) (sq_nonneg _)
  · rw [norm_mul, norm_mul, Complex.norm_ofNat, he, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hm (mul_nonneg (by norm_num only) (Real.exp_pos _).le)

/-- The grouped mass can use any degree cap, with extra coefficients equal to zero. -/
private theorem centered_mass_pad (P : Polynomial ℝ) (w : ℕ → ℝ) {n : ℕ} (hn : P.natDegree ≤ n) :
    (∑ j ∈ Finset.range (P.natDegree + 1), |principalMomentCoeff P 5 j| * w j) =
      ∑ j ∈ Finset.range (n + 1),
        |∑ k ∈ Finset.range (n + 1), P.coeff k * ((k.choose j : ℝ) * 5 ^ (k - j))| * w j := by
  have hr := Finset.range_mono (Nat.add_le_add_right hn 1)
  have hpad (j : ℕ) :
    principalMomentCoeff P 5 j =
      ∑ k ∈ Finset.range (n + 1), P.coeff k * ((k.choose j : ℝ) * 5 ^ (k - j)) := by
    unfold principalMomentCoeff
    apply Finset.sum_subset hr
    intro k _ hk
    have hk' : P.natDegree < k :=
      Nat.lt_of_not_ge (fun h ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk', zero_mul]
  simp only [← hpad]
  apply Finset.sum_subset hr
  intro j _ hj
  have hj' : P.natDegree < j :=
    Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  have hc : principalMomentCoeff P 5 j = 0 := by
    unfold principalMomentCoeff
    apply Finset.sum_eq_zero
    intro k hk
    have h := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans_lt hj'
    simp only [Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul, mul_zero]
  simp only [hc, abs_zero, zero_mul]

/-- The centered polynomial before embedding its coefficients into the reals. -/
private noncomputable def highCenteredRatPoly (K : HighGaussianKernel) : Polynomial ℚ :=
  Polynomial.C (K.pole - 1 / 2) * highRatProfile K - (highRatProfile K).derivative

/-- Mapping the rational centered polynomial gives the real one with the same support. -/
private theorem high_centered_rat_map (K : HighGaussianKernel) :
    (highCenteredRatPoly K).map (Rat.castHom ℝ) = highCenteredProfile K := by
  simp only [highCenteredRatPoly, highCenteredProfile, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, ← Polynomial.derivative_map, high_rat_profile_map, Rat.coe_castHom,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

/-- Neither centering term exceeds the original degree cap. -/
private theorem high_centered_rat_degree (K : HighGaussianKernel) :
    (highCenteredRatPoly K).natDegree ≤ 2 * K.degree + 3 := by
  unfold highCenteredRatPoly
  exact
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((Polynomial.natDegree_C_mul_le _ _).trans (high_rat_profile_degree K))
        ((Polynomial.natDegree_derivative_le _).trans
          ((Nat.sub_le _ _).trans (high_rat_profile_degree K))))

/-- The rational absolute inverse-power sum, with zero padding up to the degree cap. -/
private noncomputable def highCenteredMassRat (K : HighGaussianKernel) : ℚ :=
  let n := 2 * K.degree + 3
  let P := highCenteredRatPoly K
  ∑ j ∈ Finset.range (n + 1),
    |∑ k ∈ Finset.range (n + 1), P.coeff k * ((k.choose j : ℚ) * 5 ^ (k - j))| * (j.factorial : ℚ) /
      100 ^ j

/-- The rational mass has exactly the same value as the real grouped mass. -/
private theorem high_centered_mass_rat_eq (K : HighGaussianKernel) :
    highCenteredMass K = (highCenteredMassRat K : ℝ) := by
  have hd : (highCenteredProfile K).natDegree ≤ 2 * K.degree + 3 := by
    rw [← high_centered_rat_map]
    exact Polynomial.natDegree_map_le.trans (high_centered_rat_degree K)
  unfold highCenteredMass
  simp only [div_eq_mul_inv, mul_assoc]
  rw [centered_mass_pad _ (fun j ↦ (j.factorial : ℝ) * (100 ^ j)⁻¹) hd]
  simp only [highCenteredMassRat, Rat.cast_sum, Rat.cast_abs, Rat.cast_mul, Rat.cast_inv,
    Rat.cast_natCast, Rat.cast_pow, Rat.cast_ofNat, ← high_centered_rat_map K, Polynomial.coeff_map,
    Rat.coe_castHom, div_eq_mul_inv, mul_assoc]

/-- Rational upper evaluation of the centered tail prefactor. -/
public noncomputable def highCenteredTailRat (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  K.normalization * (highCompactRat K).1 ^ 2 / 100 ^ 2 +
    4 * headExpUpper (K.pole * 5) m * highCenteredMassRat K

/-- The finite rational charge bounds the centered analytic tail. -/
public theorem high_centered_tail_rat_le (K : HighGaussianKernel) (m : ℕ) :
    highCenteredTail K ≤ (highCenteredTailRat K m : ℝ) := by
  have ha := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have h :=
    head_exp_upper_sound (mul_nonneg (Rat.cast_pos.mp ha).le (by norm_num only : (0 : ℚ) ≤ 5)) m
  have hm : 0 ≤ highCenteredMass K :=
    Finset.sum_nonneg
      (fun j _ ↦
        div_nonneg (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
          (pow_nonneg (by norm_num only) j))
  simp only [Rat.cast_mul, Rat.cast_ofNat] at h
  rw [mul_comm (K.pole : ℝ) 5] at h
  simp only [highCenteredTail, highCenteredTailRat, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
    Rat.cast_pow, Rat.cast_ofNat, (high_compact_rat_eq K).1, ← high_centered_mass_rat_eq K]
  exact
    add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h (by norm_num only)) hm)

/-- A centered coefficient is computed from two adjacent profile coefficients. -/
private def centeredCoeff (d : ℚ) (b : ℕ → ℚ) (j : ℕ) : ℚ :=
  d * b j - b (j + 1) * (j + 1 : ℕ)

/-- The executable centered coefficient agrees with the polynomial definition. -/
private theorem centered_coeff_eq (K : HighGaussianKernel) (j : ℕ) :
    (highCenteredRatPoly K).coeff j = centeredCoeff (K.pole - 1 / 2) (highProfileCoeff K) j := by
  simp only [highCenteredRatPoly, centeredCoeff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, high_profile_coeff_eq, Nat.cast_add, Nat.cast_one]

/-- Evaluate a weighted sum of translated coefficients using integer dot products. -/
private def centeredWeightFast (K : HighGaussianKernel) (w : ℕ → ℚ) : ℚ :=
  let n := 2 * K.degree + 3
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let profile := headCoeffCache (n + 2) (highProfileFrom K compact)
  let row :=
    headAffineRow n (fun i ↦ centeredCoeff (K.pole - 1 / 2) (headCached profile) i) 5 1
      Nat.fast_choose
  ∑ j : Fin (n + 1), |row[j.val]?.getD 0| * w j

/-- The weighted executable sum agrees with the padded coefficient formula. -/
private theorem centered_weight_fast_eq (K : HighGaussianKernel) (w : ℕ → ℚ) :
    let n := 2 * K.degree + 3
    centeredWeightFast K w =
      ∑ j ∈ Finset.range (n + 1),
        |∑ k ∈ Finset.range (n + 1),
              (highCenteredRatPoly K).coeff k * ((k.choose j : ℚ) * 5 ^ (k - j))| *
          w j := by
  simp only [centeredWeightFast, head_coeff_cache_eq, head_affine_row_eq, one_pow, one_mul]
  simp only [centered_coeff_eq, highProfileCoeff, ← Nat.choose_eq_fast_choose,
    ← Fin.sum_univ_eq_sum_range]

/-- The executable sum specializes to the inverse-power weights at height 100. -/
private def centeredMassFast (K : HighGaussianKernel) : ℚ :=
  centeredWeightFast K (fun j ↦ (j.factorial : ℚ) / 100 ^ j)

/-- The accelerated sum is the same rational upper bound. -/
private theorem centered_mass_fast_eq (K : HighGaussianKernel) :
    centeredMassFast K = highCenteredMassRat K := by
  simp only [centeredMassFast, centered_weight_fast_eq, highCenteredMassRat, mul_div_assoc]

/-- The executable prefactor consists of the compact square and the centered moment. -/
private def centeredTailFast (K : HighGaussianKernel) : ℚ :=
  K.normalization * (highCompactRat K).1 ^ 2 / 100 ^ 2 +
    4 * headExpUpper (K.pole * 5) 36 * centeredMassFast K

/-- The executable prefactor computes the certified rational expression at Taylor degree 36. -/
private theorem centered_tail_fast_eq (K : HighGaussianKernel) :
    centeredTailFast K = highCenteredTailRat K 36 := by
  simp only [centeredTailFast, highCenteredTailRat, centered_mass_fast_eq]

/-- The centered tail charge is nonnegative. -/
private theorem high_centered_tail_nonneg (K : HighGaussianKernel) : 0 ≤ highCenteredTail K := by
  have h := (norm_nonneg _).trans (high_centered_tail_le K (by norm_num only : (100 : ℝ) < 101))
  have he := mul_nonneg h (by norm_num only : (0 : ℝ) ≤ 101 ^ 2)
  rwa [div_mul_cancel₀ _ (by norm_num only : (101 : ℝ) ^ 2 ≠ 0)] at he

/-- The full series is controlled by the 29 midpoint norms and the centered rational tail. -/
public theorem high_centered_series_le (K : HighGaussianKernel) (hRH : RiemannHypothesis) (m : ℕ)
    (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        (highCenteredTailRat K m : ℝ) * (13 / 1000) := by
  exact
    (high_principal_series_le K hRH (high_centered_tail_nonneg K) hc
          (fun _ ht ↦ high_centered_tail_le K ht) hX).trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (high_centered_tail_rat_le K m) (by norm_num only)))

end PseudoPrime.PrimeTestBounds.MillerRabin
