/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadNumeric
import Mathlib.Tactic.Ring

/-! # Rational certification of the principal Gaussian tail charge -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The derivative polynomial after factoring out the exponential rate. -/
private noncomputable def tailRatDeriv (a : ℚ) (P : Polynomial ℚ) : Polynomial ℚ :=
  P.derivative - Polynomial.C a * P

/-- The derivative construction commutes with the rational-to-real cast. -/
private theorem tail_rat_deriv_map (a : ℚ) (P : Polynomial ℚ) :
    (tailRatDeriv a P).map (Rat.castHom ℝ) = tailDerivative a (P.map (Rat.castHom ℝ)) := by
  simp only [tailRatDeriv, tailDerivative, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    ← Polynomial.derivative_map, Rat.coe_castHom]

/-- Factoring out the exponential does not increase the polynomial degree. -/
private theorem tail_rat_deriv_degree (a : ℚ) (P : Polynomial ℚ) :
    (tailRatDeriv a P).natDegree ≤ P.natDegree := by
  exact
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((Polynomial.natDegree_derivative_le P).trans (Nat.sub_le _ _))
        (Polynomial.natDegree_C_mul_le _ _))

/-- The second derivative polynomial has degree at most that of the profile. -/
private theorem tail_rat_second_degree (K : HighGaussianKernel) :
    (tailRatDeriv K.pole (tailRatDeriv K.pole (highRatProfile K))).natDegree ≤ 2 * K.degree + 3 :=
  (tail_rat_deriv_degree _ _).trans ((tail_rat_deriv_degree _ _).trans (high_rat_profile_degree K))

/-- The norm of a weighted amplitude is its positive exponential times the absolute polynomial. -/
private theorem tail_amplitude_norm (a v : ℝ) (P : Polynomial ℝ) :
    ‖tailAmplitude a P v‖ = Real.exp (-a * v) * |P.eval v| := by
  simp only [tailAmplitude, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]

/-- The weighted Bernstein upper sum for the absolute second derivative. -/
private noncomputable def tailIntegralRat (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  let n := 2 * K.degree + 3
  let P := tailRatDeriv K.pole (tailRatDeriv K.pole (highRatProfile K))
  ∑ j ∈ Finset.range 32,
    headExpUpper (K.pole * highHeadGrid j) m *
      ((highHeadGrid (j + 1) - highHeadGrid j) *
        ((∑ k : Fin (n + 1),
            |Analysis.bernsteinRatCoeff
                (P.comp
                  (Polynomial.C (highHeadGrid (j + 1) - highHeadGrid j) * Polynomial.X +
                    Polynomial.C (highHeadGrid j)))
                n k|) /
          ((n : ℚ) + 1)))

/-- The weighted second derivative integral is bounded by its rational Bernstein sum. -/
private theorem tail_integral_rat_le (K : HighGaussianKernel) (m : ℕ) :
    let B := K.realProfile
    let a := (K.pole : ℝ)
    (∫ v in (0 : ℝ)..5, ‖tailAmplitude a (tailDerivative a (tailDerivative a B)) v‖) ≤
      (tailIntegralRat K m : ℝ) := by
  intro B a
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have hq := Rat.cast_pos.mp ha
  have hp (j : ℕ) : highHeadGrid j < highHeadGrid (j + 1) := by
    unfold highHeadGrid
    exact
      div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left (Nat.cast_lt.mpr (Nat.lt_succ_self j)) (by norm_num only))
        (by norm_num only)
  have he (j : ℕ) :
    Real.exp (-a * (highHeadGrid j : ℝ)) ≤ (headExpUpper (K.pole * highHeadGrid j) m : ℝ) := by
    have hgrid : 0 ≤ highHeadGrid j := by
      unfold highHeadGrid
      exact div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (by norm_num only)
    simpa only [a, Rat.cast_mul, neg_mul] using head_exp_upper_sound (mul_nonneg hq.le hgrid) m
  have h :=
    Analysis.weighted_abs_rat_bernstein
      (tailRatDeriv K.pole (tailRatDeriv K.pole (highRatProfile K))) 32 (2 * K.degree + 3)
      (tail_rat_second_degree K) ha.le highHeadGrid
      (fun j ↦ headExpUpper (K.pole * highHeadGrid j) m) (fun j _ ↦ hp j) (fun j _ ↦ he j)
  have hzero : highHeadGrid 0 = 0 := by
    norm_num only [highHeadGrid, Nat.cast_zero, mul_zero, zero_div]
  have hlast : highHeadGrid 32 = 5 := by norm_num only [highHeadGrid, Nat.cast_ofNat]
  simp only [hzero, hlast, Rat.cast_zero, Rat.cast_ofNat] at h
  simpa only [tailIntegralRat, tail_amplitude_norm, a, B, ← Polynomial.eval_map, tail_rat_deriv_map,
    high_rat_profile_map] using h

/-- The second weighted derivative coefficient is evaluated directly from the profile. -/
private theorem tail_rat_second_coeff (K : HighGaussianKernel) (k : ℕ) :
    (tailRatDeriv K.pole (tailRatDeriv K.pole (highRatProfile K))).coeff k =
      highHeadInnerCoeff K.pole (highProfileCoeff K) k := by
  simp only [tailRatDeriv, highHeadInnerCoeff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative, high_profile_coeff_eq, Nat.cast_add, Nat.cast_one]
  ring

/-- Evaluate the tail integral using the shared coefficient and binomial caches. -/
private def tailIntegralFast (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  let n := 2 * K.degree + 3
  let choose := headCoeffCache (n + 1) (fun k ↦ headCoeffCache (n + 1) (Nat.fast_choose k))
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let profile := headCoeffCache (n + 3) (highProfileFrom K compact)
  let coeffs := headCoeffCache (n + 1) (highHeadInnerCoeff K.pole (headCached profile))
  ∑ j ∈ Finset.range 32,
    let l := highHeadGrid j
    headExpUpper (K.pole * l) m *
      headCellMass n (fun i ↦ headCached coeffs i) l (highHeadGrid (j + 1) - l)
        (fun k i ↦ headCached (headCached choose k) i)

/-- The executable tail integral agrees with the rational polynomial upper sum. -/
private theorem tail_integral_fast_eq (K : HighGaussianKernel) (m : ℕ) :
    tailIntegralFast K m = tailIntegralRat K m := by
  simp only [tailIntegralFast, head_coeff_cache_eq, head_cell_mass_eq]
  simp only [highProfileCoeff, tailIntegralRat, Analysis.bernsteinRatCoeff,
    Analysis.rational_affine_coeff _ _ (tail_rat_second_degree K), tail_rat_second_coeff,
    ← Nat.choose_eq_fast_choose, ← Fin.sum_univ_eq_sum_range]

/-- At five the exponential and the polynomial value admit a rational charge. -/
private theorem tail_endpoint_rat_le (K : HighGaussianKernel) (m : ℕ) (P : Polynomial ℚ) :
    ‖tailAmplitude K.pole (P.map (Rat.castHom ℝ)) 5‖ ≤
      ((headExpUpper (K.pole * 5) m * |P.eval 5| : ℚ) : ℝ) := by
  have ha : 0 < (K.pole : ℝ) := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have h :=
    head_exp_upper_sound (mul_nonneg (Rat.cast_pos.mp ha).le (by norm_num only : (0 : ℚ) ≤ 5)) m
  have he : ((P.eval (5 : ℚ) : ℚ) : ℝ) = (P.map (Rat.castHom ℝ)).eval 5 := by
    simpa only [Rat.coe_castHom, Rat.cast_ofNat] using
      (Polynomial.eval_map_apply (p := P) (Rat.castHom ℝ) (5 : ℚ)).symm
  rw [tail_amplitude_norm, ← he]
  simp only [Rat.cast_mul, Rat.cast_abs]
  simp only [Rat.cast_mul, Rat.cast_ofNat, ← neg_mul] at h
  exact mul_le_mul_of_nonneg_right h (abs_nonneg _)

/-- A rational upper bound on the positive-height inverse-square prefactor.
It charges the compact square, the derivative endpoint, the integral, and half the middle term. -/
public noncomputable def highPrincipalTailRat (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  3 * K.normalization * (highCompactRat K).1 ^ 2 / 100 ^ 2 +
    4 *
      (headExpUpper (K.pole * 5) m * |(tailRatDeriv K.pole (highRatProfile K)).eval 5| +
        tailIntegralRat K m +
        (90202 / 1000000) / 2)

/-- Evaluate the first weighted derivative at the right endpoint from its coefficients. -/
private def tailEndpointFast (K : HighGaussianKernel) : ℚ :=
  let n := 2 * K.degree + 3
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let profile := headCoeffCache (n + 2) (highProfileFrom K compact)
  let b := headCached profile
  ∑ i ∈ Finset.range (n + 1), (b (i + 1) * (i + 1 : ℕ) - K.pole * b i) * (5 : ℚ) ^ i

/-- The executable endpoint is the evaluation of the first derivative polynomial. -/
private theorem tail_endpoint_fast_eq (K : HighGaussianKernel) :
    tailEndpointFast K = (tailRatDeriv K.pole (highRatProfile K)).eval 5 := by
  have hd := (tail_rat_deriv_degree K.pole (highRatProfile K)).trans (high_rat_profile_degree K)
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  simp only [tailEndpointFast, head_coeff_cache_eq, tailRatDeriv, Polynomial.coeff_sub,
    Polynomial.coeff_derivative, Polynomial.coeff_C_mul, high_profile_coeff_eq, highProfileCoeff,
    Nat.cast_add, Nat.cast_one]

/-- Executable rational upper bound for the inverse-square tail prefactor. -/
private def highPrincipalTailFast (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  3 * K.normalization * (highCompactRat K).1 ^ 2 / 100 ^ 2 +
    4 *
      (headExpUpper (K.pole * 5) m * |tailEndpointFast K| + tailIntegralFast K m +
        (90202 / 1000000) / 2)

/-- The executable prefactor gives the same certified upper bound. -/
private theorem high_principal_tail_fast_eq (K : HighGaussianKernel) (m : ℕ) :
    highPrincipalTailFast K m = highPrincipalTailRat K m := by
  simp only [highPrincipalTailFast, highPrincipalTailRat, tail_endpoint_fast_eq,
    tail_integral_fast_eq]

/-- The analytic prefactor is bounded by the fully rational expression. -/
public theorem high_principal_tail_rat_le (K : HighGaussianKernel) (m : ℕ) :
    highPrincipalTailCharge K ≤ (highPrincipalTailRat K m : ℝ) := by
  have hd := tail_endpoint_rat_le K m (tailRatDeriv K.pole (highRatProfile K))
  rw [tail_rat_deriv_map, high_rat_profile_map, Rat.cast_mul] at hd
  have hi := tail_integral_rat_le K m
  have he : ‖tailAmplitude K.pole K.realProfile 5‖ = |highPrincipalEdge K| := by
    rw [tail_amplitude_norm, highPrincipalEdge, abs_mul, abs_of_pos (Real.exp_pos _), neg_mul,
      neg_mul, mul_comm (5 : ℝ)]
  unfold highPrincipalTailCharge highTailHeadCharge highPrincipalTailRat
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    (high_compact_rat_eq K).1]
  exact
    add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add hd hi)
          (div_le_div_of_nonneg_right (he.trans_le (high_principal_edge_cap K)) (by norm_num only)))
        (by norm_num only))

/-- The normalized principal series uses a tail budget computed with rational arithmetic. -/
public theorem high_principal_series_rat_le (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    (m : ℕ) (hc : highPrincipalHeadCap K ≤ (highHeadCapTicks K : ℝ) / 1000) {X : ℝ} (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    |Real.exp (-(5 * (K.pole : ℝ))) *
          (principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) /
            Real.sqrt X)| ≤
      2 *
          ((∑ i, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) +
            (highZeroErrorBudget K : ℝ)) +
        (highPrincipalTailRat K m : ℝ) * (13 / 1000) := by
  exact
    (high_principal_series_tail_le K hRH hc hX).trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right (high_principal_tail_rat_le K m) (by norm_num only)))

end PseudoPrime.PrimeTestBounds.MillerRabin
