/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import Mathlib.Tactic

/-! # Curvature of the lower K131 reflection moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem monomial_curvature_quad {v j : ℝ} (hv : 47 / 2 ≤ v) (hj : j ≤ 19) :
    0 ≤ 621 / 16 * v ^ 2 - 50 * j * v + 16 * j * (j - 1) := by
  have h₁ : 0 ≤ 621 / 16 * (v + 47 / 2) - 50 * j := by linarith only [hv, hj]
  have h₂ : 0 ≤ 50 * (47 / 2 : ℝ) - 16 * (j + 18) := by linarith only [hj]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hv) h₁, mul_nonneg (sub_nonneg.mpr hj) h₂]

/-- An affine power of degree at most nineteen has nonnegative K131
reflection curvature once its argument reaches 47/2. -/
theorem reflection_power_curvature (h x : ℝ) {n : ℕ} (hn : n ≤ 19) (hx : 47 / 2 ≤ 2 * x - h) :
    0 ≤
      (logPowerCurvature (23 / 4) ((Polynomial.C 2 * Polynomial.X - Polynomial.C h) ^ n)).eval
        x := by
  let S : Polynomial ℝ := Polynomial.C 2 * Polynomial.X - Polynomial.C h
  let v := 2 * x - h
  have hs : S.eval x = v := by
    simp only [S, v, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have hd : S.derivative = Polynomial.C 2 := by
    simp only [S, Polynomial.derivative_sub, Polynomial.derivative_C_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, mul_one, sub_zero]
  change 0 ≤ (logPowerCurvature (23 / 4) (S ^ n)).eval x
  cases n with
  | zero =>
    norm_num only [logPowerCurvature, pow_zero, Polynomial.derivative_one,
      Polynomial.derivative_zero, mul_zero, sub_zero, add_zero, mul_one, Polynomial.eval_C]
  | succ n =>
    cases n with
    | zero =>
      change 0 ≤ (logPowerCurvature (23 / 4) (S ^ 1)).eval x
      simp only [logPowerCurvature, pow_one, hd, Polynomial.derivative_C, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, hs, mul_zero, add_zero]
      linarith only [show (47 / 2 : ℝ) ≤ v from hx]
    | succ n =>
      have hcast : (n : ℝ) + 2 ≤ 19 := by exact_mod_cast hn
      have hq := monomial_curvature_quad (v := v) (j := (n : ℝ) + 2) hx hcast
      have hv : 0 ≤ v := by linarith only [hx]
      have hD₁ :
        (S ^ (n + 1 + 1)).derivative =
          Polynomial.C ((n : ℝ) + 1 + 1) * S ^ (n + 1) * Polynomial.C 2 := by
        rw [Polynomial.derivative_pow_succ, hd, Nat.cast_add, Nat.cast_one]
      have hD₂ :
        (S ^ (n + 1)).derivative = Polynomial.C ((n : ℝ) + 1) * S ^ n * Polynomial.C 2 := by
        rw [Polynomial.derivative_pow_succ, hd]
      have he :
        (logPowerCurvature (23 / 4) (S ^ (n + 1 + 1))).eval x =
          v ^ n *
            (621 / 16 * v ^ 2 - 50 * ((n : ℝ) + 2) * v +
              16 * ((n : ℝ) + 2) * ((n : ℝ) + 2 - 1)) := by
        rw [logPowerCurvature, hD₁, Polynomial.derivative_mul, Polynomial.derivative_C_mul, hD₂,
          Polynomial.derivative_C, mul_zero, add_zero]
        simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
          Polynomial.eval_pow, hs, pow_succ]
        ring
      rw [he]
      exact mul_nonneg (pow_nonneg hv _) hq

private theorem curvature_scale (p c x : ℝ) (P : Polynomial ℝ) :
    (logPowerCurvature p (Polynomial.C c * P)).eval x = c * (logPowerCurvature p P).eval x := by
  simp only [logPowerCurvature, Polynomial.derivative_C_mul, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
  ring

private theorem curvature_sum {ι : Type*} (p x : ℝ) (s : Finset ι) (P : ι → Polynomial ℝ) :
    (logPowerCurvature p (∑ i ∈ s, P i)).eval x = ∑ i ∈ s, (logPowerCurvature p (P i)).eval x := by
  simp only [logPowerCurvature, Polynomial.derivative_sum, Polynomial.eval_finsetSum,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

private theorem inverse_coeff_nonneg (n : ℕ) : 0 ≤ gaussianK131InversePoly.coeff n := by
  rw [gaussianK131InversePoly, Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro j _
  rw [Polynomial.coeff_monomial]
  simp only [Finsupp.single_apply]
  split
  · exact Rat.cast_nonneg.mpr ((show ∀ k : Fin 9, 0 ≤ inverseCoeffs k by decide +kernel) j)
  · exact le_rfl

private theorem inverse_degree_le : gaussianK131InversePoly.natDegree ≤ 19 := by
  unfold gaussianK131InversePoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  refine Polynomial.natDegree_monomial_le _ |>.trans ?_
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt)) 3

private theorem reflected_moment_curvature (h x : ℝ) (hx : 47 / 2 ≤ 2 * x - h) :
    0 ≤
      (logPowerCurvature (23 / 4)
            ((k131MomentPoly gaussianK131InversePoly (19 / 16) 0).comp
              (Polynomial.C 2 * Polynomial.X - Polynomial.C h))).eval
        x := by
  unfold k131MomentPoly
  rw [Polynomial.sum_comp, curvature_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Polynomial.mul_comp, Polynomial.C_comp, curvature_scale]
  apply mul_nonneg (by positivity)
  rw [Polynomial.iterate_derivative_eq_sum, Polynomial.sum_comp, curvature_sum]
  apply Finset.sum_nonneg
  intro n hn
  rw [Polynomial.mul_comp, Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp,
    curvature_scale]
  have hn' := Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)
  have hN := hn'.trans (Polynomial.natDegree_iterate_derivative _ _)
  refine
    mul_nonneg ?_
      (reflection_power_curvature h x (hN.trans ((Nat.sub_le _ _).trans inverse_degree_le)) hx)
  rw [nsmul_eq_mul]
  exact mul_nonneg (Nat.cast_nonneg _) (inverse_coeff_nonneg _)

private theorem reflection_offset_le (j : Fin 2) : reflectionOffsets j ≤ 9 / 2 := by
  fin_cases j
  · change (1 / 10 : ℝ) ≤ 9 / 2
    norm_num only
  · exact le_rfl

private theorem reflect_factor_nonpos (j : Fin 2) : reflectFactor j ≤ 0 := by
  have hA : (0 : ℝ) ≤ gaussianK131Amplitude := by
    rw [k131_amplitude_eq]; positivity
  have hν : 0 ≤ reflectionWeights j := by
    fin_cases j
    · change 0 ≤ (973 / 5000 : ℝ) - 1831 / 10000 * Real.exp (-(27 / 16) * (1 / 10))
      have he := Real.exp_le_one_iff.mpr (by norm_num only : (-(27 / 16 : ℝ) * (1 / 10)) ≤ 0)
      linarith only [he]
    · change 0 ≤ (13 / 1250 : ℝ) - 1 / 80 * Real.exp (-(27 / 16) * (12 / 5))
      have he : Real.exp (-(27 / 16 : ℝ) * (12 / 5)) ≤ 1 / 2 := by
        rw [neg_mul, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
        have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ (27 / 16) * (12 / 5)) 2
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, div_one, zero_add] at ht
        linarith only [ht]
      linarith only [he]
  unfold reflectFactor
  exact
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by norm_num only) hν) hA)
      (Real.exp_pos _).le

/-- The normalized curvature of the actual K131 lower reflection moment
is nonpositive over the whole logarithmic range of the bridge. -/
theorem gaussian_k131_poly23_curvature {y : ℝ} (hy : 0 < y) (hlog : 14 ≤ 2 * Real.log y) :
    logPowerPoly (-(23 / 4 : ℝ)) (logPowerCurvature (23 / 4) gaussianK131Poly23) y ≤ 0 := by
  unfold logPowerPoly gaussianK131Poly23
  apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hy.le _)
  rw [curvature_sum]
  apply Finset.sum_nonpos
  intro j _
  rw [curvature_scale]
  apply mul_nonpos_of_nonpos_of_nonneg (reflect_factor_nonpos j)
  unfold reflectPoly
  exact reflected_moment_curvature _ _ (by linarith only [hlog, reflection_offset_le j])

/-- Discharge the lower reflection sign in the instantiated K131 gap
comparison. Only the other three curvature signs and endpoint checks remain. -/
theorem gaussian_k131_gap_of_signs {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsign :
      ∀ y ∈ Set.Ioo (465644807 / 400000 : ℝ) (1036273 / 250),
        logPowerPoly (-(19 / 8 : ℝ)) (logPowerCurvature (19 / 8) gaussianK131Poly19) y ≤ -1 ∧
          logPowerPoly (-(27 / 8 : ℝ)) (logPowerCurvature (27 / 8) gaussianK131Poly27) y ≤ 0 ∧
          logPowerPoly (-(27 / 4 : ℝ)) (logPowerCurvature (27 / 4) gaussianK131PolyHigher) y ≤ 0)
    (hleft : 1 / 200 < gaussianK131Gap (465644807 / 400000))
    (hright : 1 / 200 < gaussianK131Gap (1036273 / 250)) :
    1 / 200 < gaussianK131Gap (gaussianBridgeScale L) := by
  apply gaussian_k131_gap_pos hL _ hleft hright
  intro y hy
  obtain ⟨h₁, h₂, h₄⟩ := hsign y hy
  refine
    ⟨h₁, h₂,
      gaussian_k131_poly23_curvature ((by norm_num only : (0 : ℝ) < 465644807 / 400000).trans hy.1)
        ?_,
      h₄⟩
  let U := (y + 123 / 10) / (519674 / 1000000 : ℝ)
  have hU : U ∈ Set.Icc (9055 / 4 : ℝ) 8000 := by
    dsimp only [U]
    exact ⟨by linarith only [hy.1], by linarith only [hy.2]⟩
  have he : gaussianBridgeScale U = y := by
    dsimp only [gaussianBridgeScale, U]; ring
  exact (he ▸ k131_radius_log_mem hU).1

end PseudoPrime.PrimeTestBounds.MillerRabin
