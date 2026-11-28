/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ContourBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GammaMajorant

/-! # Exponential decay of the K186 Abel tail -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Differentiation of the finite geometric derivative sum cancels every
term except the original profile. The next derivative beyond the degree vanishes. -/
theorem k186_gamma_geometric_derivative :
    k186GammaGeometricPoly.derivative =
      Polynomial.C (7 / 4 : ℝ) *
        (k186GammaGeometricPoly - Polynomial.C 2 * HighGaussianKernel.k186.realProfile) := by
  let B := HighGaussianKernel.k186.realProfile
  let N := B.natDegree
  let r : ℝ := 4 / 7
  let F (j : ℕ) := Polynomial.C (2 * r ^ j) * (Polynomial.derivative^[j]) B
  have hG : k186GammaGeometricPoly = ∑ j ∈ Finset.range (N + 1), F j := rfl
  have hF (j : ℕ) :
    Polynomial.C (7 / 4 : ℝ) * F (j + 1) =
      Polynomial.C (2 * r ^ j) * (Polynomial.derivative^[j + 1]) B := by
    simp only [F, ← mul_assoc, ← Polynomial.C_mul, pow_succ]
    congr 2
    dsimp only [r]
    ring
  rw [hG, Polynomial.derivative_sum, Finset.sum_range_succ]
  rw [Finset.sum_range_succ' F,
    show F 0 = Polynomial.C 2 * B by simp only [F, pow_zero, mul_one, Function.iterate_zero, id_eq],
    add_sub_cancel_right, Finset.mul_sum]
  simp only [F, Polynomial.derivative_C_mul, ← Function.iterate_succ_apply']
  rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self N), mul_zero, add_zero]
  exact Finset.sum_congr rfl fun j _ ↦ (hF j).symm

/-- The normalized geometric majorant decreases on the positive profile
ray because its derivative is a negative multiple of the profile. -/
theorem k186_geometric_decay_antitone :
    AntitoneOn (fun z : ℝ ↦ Real.exp (-(7 / 4 : ℝ) * z) * k186GammaGeometricPoly.eval z)
      (Set.Ici 65) := by
  have hd (z : ℝ) :
    HasDerivAt (fun v : ℝ ↦ Real.exp (-(7 / 4 : ℝ) * v) * k186GammaGeometricPoly.eval v)
      (-(7 / 2 : ℝ) * Real.exp (-(7 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z)
      z := by
    have he := ((hasDerivAt_id z).const_mul (-(7 / 4) : ℝ)).exp
    have hp := k186GammaGeometricPoly.hasDerivAt z
    convert he.mul hp using 1
    · rfl
    · rw [k186_gamma_geometric_derivative]
      simp only [id_eq, mul_one, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
      ring
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun z _ ↦ (hd z).continuousAt.continuousWithinAt
  · exact fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
  · intro z hz
    rw [(hd z).deriv]
    have hs :=
      high_int_profile_sign .k186 65 k186_profile_grid_check 0
        (show ((65 : ℤ) : ℝ) ≤ z from interior_subset hz)
    simp only [Function.iterate_zero, id_eq] at hs
    exact
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num only) (Real.exp_nonneg _)) hs

/-- The existing anchor certificate supplies an integrable exponential
majorant for the damped geometric profile. -/
theorem k186_geometric_ray_decay {z : ℝ} (hz : 65 ≤ z) :
    Real.exp (-(11 / 4 : ℝ) * z) * k186GammaGeometricPoly.eval z ≤
      (1 / 10 ^ 6 : ℝ) * Real.exp (65 - z) := by
  have h :=
    k186_geometric_decay_antitone (Set.mem_Ici.mpr (le_refl (65 : ℝ))) (Set.mem_Ici.mpr hz) hz
  change
    Real.exp (-(7 / 4 : ℝ) * z) * k186GammaGeometricPoly.eval z ≤
      Real.exp (-(7 / 4 : ℝ) * 65) * k186GammaGeometricPoly.eval 65 at h
  have h₀ := k186_gamma_geometric_ray_le (le_refl (65 : ℝ))
  calc
    _ = Real.exp (-z) * (Real.exp (-(7 / 4 : ℝ) * z) * k186GammaGeometricPoly.eval z) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-z) * (Real.exp (-(7 / 4 : ℝ) * 65) * k186GammaGeometricPoly.eval 65) :=
      mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    _ = (Real.exp (-(11 / 4 : ℝ) * 65) * k186GammaGeometricPoly.eval 65) * Real.exp (65 - z) := by
      have he :
        Real.exp (-z) * Real.exp (-(7 / 4 : ℝ) * 65) =
          Real.exp (-(11 / 4 : ℝ) * 65) * Real.exp (65 - z) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [← mul_assoc, he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h₀ (Real.exp_nonneg _)

/-- On the certified sign ray, each of the first three derivatives is
bounded by twice the geometric majorant. -/
private theorem k186_profile_deriv_le_geometric {z : ℝ} (hz : 65 ≤ z) (j : Fin 3) :
    ((Polynomial.derivative^[j.val]) HighGaussianKernel.k186.realProfile).eval z ≤
      2 * k186GammaGeometricPoly.eval z := by
  let B := HighGaussianKernel.k186.realProfile
  let f (k : ℕ) := 2 * (4 / 7 : ℝ) ^ k * ((Polynomial.derivative^[k]) B).eval z
  have hs (k : ℕ) : 0 ≤ ((Polynomial.derivative^[k]) B).eval z :=
    high_int_profile_sign .k186 65 k186_profile_grid_check k (show ((65 : ℤ) : ℝ) ≤ z from hz)
  have hf (k : ℕ) : 0 ≤ f k :=
    mul_nonneg (mul_nonneg (by norm_num only) (pow_nonneg (by norm_num only) _)) (hs k)
  have he : k186GammaGeometricPoly.eval z = ∑ k ∈ Finset.range (B.natDegree + 1), f k := by
    simp only [k186GammaGeometricPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, B, f]
  rw [he]
  by_cases hj : j.val < B.natDegree + 1
  · have hsum := Finset.single_le_sum (f := f) (fun k _ ↦ hf k) (Finset.mem_range.mpr hj)
    have hw : (1 / 2 : ℝ) ≤ 2 * (4 / 7 : ℝ) ^ j.val := by fin_cases j <;> norm_num only
    have hm := mul_le_mul_of_nonneg_right hw (hs j)
    dsimp only [f] at hsum
    linarith only [hsum, hm]
  · rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_of_succ_le (Nat.le_of_not_gt hj)),
      Polynomial.eval_zero]
    exact mul_nonneg (by norm_num only) (Finset.sum_nonneg fun k _ ↦ hf k)

/-- The second-order Abel polynomial on the ray is dominated by the
geometric majorant with a uniform factor of 32. -/
private theorem k186_abel_poly_abs_le {z : ℝ} (hz : 65 ≤ z) :
    let B := HighGaussianKernel.k186.realProfile
    let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
    let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
    |D.eval z| ≤ 32 * k186GammaGeometricPoly.eval z := by
  intro B Q D
  have hs (k : ℕ) : 0 ≤ ((Polynomial.derivative^[k]) B).eval z :=
    high_int_profile_sign .k186 65 k186_profile_grid_check k (show ((65 : ℤ) : ℝ) ≤ z from hz)
  have h0 := k186_profile_deriv_le_geometric hz (0 : Fin 3)
  have h1 := k186_profile_deriv_le_geometric hz (1 : Fin 3)
  have h2 := k186_profile_deriv_le_geometric hz (2 : Fin 3)
  have h0' := hs 0
  have h1' := hs 1
  have h2' := hs 2
  change 0 ≤ B.eval z at h0'
  change 0 ≤ B.derivative.eval z at h1'
  change 0 ≤ B.derivative.derivative.eval z at h2'
  have he :
    D.eval z =
      (9 / 4 : ℝ) ^ 2 * B.eval z - (9 / 2 : ℝ) * B.derivative.eval z +
        B.derivative.derivative.eval z := by
    simp only [D, Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.derivative_sub, Polynomial.derivative_C_mul]
    ring
  rw [he]
  change B.eval z ≤ 2 * k186GammaGeometricPoly.eval z at h0
  change B.derivative.eval z ≤ 2 * k186GammaGeometricPoly.eval z at h1
  change B.derivative.derivative.eval z ≤ 2 * k186GammaGeometricPoly.eval z at h2
  apply abs_le.mpr
  constructor <;> linarith only [h0, h1, h2, h0', h1', h2']

/-- The Abel tail after 65 costs at most one, uniformly in its upper
endpoint. The existing Gamma certificate provides the only numerical input. -/
theorem k186_abel_tail_le_one {z : ℝ} (hz : 65 ≤ z) :
    let B := HighGaussianKernel.k186.realProfile
    let Q := Polynomial.C (9 / 4 : ℝ) * B - B.derivative
    let D := Polynomial.C (9 / 4 : ℝ) * Q - Q.derivative
    (∫ v in (65 : ℝ)..z, Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v|) ≤ 1 := by
  intro B Q D
  have hf : Continuous (fun v : ℝ ↦ Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul D.continuous.abs
  have hg : Continuous (fun v : ℝ ↦ (32 / 10 ^ 6 : ℝ) * Real.exp (65 - v)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.sub continuous_id))
  calc
    _ ≤ ∫ v in (65 : ℝ)..z, (32 / 10 ^ 6 : ℝ) * Real.exp (65 - v) := by
      apply
        intervalIntegral.integral_mono_on hz (hf.intervalIntegrable 65 z)
          (hg.intervalIntegrable 65 z)
      intro v hv
      have h₁ :=
        mul_le_mul_of_nonneg_left (k186_abel_poly_abs_le hv.1) (Real.exp_nonneg (-(11 / 4 : ℝ) * v))
      have h₂ :=
        mul_le_mul_of_nonneg_left (k186_geometric_ray_decay hv.1) (by norm_num only : (0 : ℝ) ≤ 32)
      change Real.exp (-(11 / 4 : ℝ) * v) * |D.eval v| ≤ _ at h₁
      linarith only [h₁, h₂]
    _ ≤ _ := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left, sub_self,
        integral_exp, Real.exp_zero]
      linarith only [Real.exp_nonneg (65 - z)]

end PseudoPrime.PrimeTestBounds.MillerRabin
