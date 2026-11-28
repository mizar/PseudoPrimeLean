/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FarBudget
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ConductorCert
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighWitness
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186DirectComparison
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget

/-! # Far K186 reflected budgets from one shifted profile -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational majorant for the maximum of an exponentially decaying monomial
on the nonnegative ray. The logarithm inequality gives its exact maximum first. -/
theorem decay_monomial_le {b u : ℝ} (hb : 0 < b) (hu : 0 ≤ u) (i : ℕ) :
    Real.exp (-b * u) * u ^ i ≤ ((3 / 8 : ℝ) * i / b) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, mul_one]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) hu)
  rcases hu.eq_or_lt with h | h
  · rw [← h, zero_pow hi.ne', mul_zero]
    exact pow_nonneg (div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) hb.le) _
  let v : ℝ := (i : ℝ) / b
  have hv : 0 < v := div_pos (Nat.cast_pos.mpr hi) hb
  have huq := div_pos h hv
  have hlog := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos huq) (Nat.cast_nonneg i)
  have he : (i : ℝ) * (u / v - 1) = b * u - i := by
    have hn : (i : ℝ) ≠ 0 := (Nat.cast_pos.mpr hi : (0 : ℝ) < i).ne'
    dsimp only [v]
    field_simp [hb.ne', hn]
  rw [he] at hlog
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_natCast_mul, Real.exp_log huq, div_pow] at hh
  have hh' := (div_le_iff₀ (pow_pos hv i)).mp hh
  have hmax : Real.exp (-b * u) * u ^ i ≤ Real.exp (-(i : ℝ)) * v ^ i := by
    refine (mul_le_mul_of_nonneg_left hh' (Real.exp_pos _).le).trans_eq ?_
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have h₁ : Real.exp (-1 : ℝ) ≤ 3 / 8 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num only)]
    exact (by norm_num only : (3 / 8 : ℝ)⁻¹ ≤ 2.7182818283).trans Real.exp_one_gt_d9.le
  refine hmax.trans ?_
  rw [show -(i : ℝ) = (i : ℝ) * (-1) by ring, Real.exp_natCast_mul, ← mul_pow]
  apply pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le hv.le)
  simpa only [v, mul_div_assoc] using mul_le_mul_of_nonneg_right h₁ hv.le

/-- The one-sided coefficient sum in a translated coordinate bounds the
decaying polynomial on the entire ray, including profiles of changing sign. -/
theorem decay_poly_le_shifted (P : Polynomial ℝ) {b z₀ z : ℝ} (hb : 0 < b) (hz : z₀ ≤ z) :
    let Q := P.comp (Polynomial.X + Polynomial.C z₀)
    Real.exp (-b * z) * P.eval z ≤
      Real.exp (-b * z₀) *
        ∑ i ∈ Finset.range (Q.natDegree + 1), max 0 (Q.coeff i) * ((3 / 8 : ℝ) * i / b) ^ i := by
  intro Q
  have he : P.eval z = Q.eval (z - z₀) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      sub_add_cancel]
  rw [he, show -b * z = -b * z₀ + -b * (z - z₀) by ring, Real.exp_add, mul_assoc,
    Polynomial.eval_eq_sum_range, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply Finset.sum_le_sum
  intro i _
  rw [mul_left_comm]
  have h := decay_monomial_le hb (sub_nonneg.mpr hz) i
  exact
    (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (mul_nonneg (Real.exp_pos _).le (pow_nonneg (sub_nonneg.mpr hz) _))).trans
      (mul_le_mul_of_nonneg_left h (le_max_left _ _))

/-- The conductor reflection at the direct cutoff has decay rate nine
quarters after the linear input factor is absorbed into the exponential. -/
theorem k186_reflected_conductor_eq {L : ℝ} (hL : 0 < L) :
    let y := gaussianK186FarScale * L
    let z := 5 + Real.log (y ^ 2)
    2 * L * Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * z) *
        HighGaussianKernel.k186.realProfile.eval z =
      (2 / gaussianK186FarScale * Real.exp (-(5 / 2 : ℝ))) *
        (Real.exp (-(9 / 4 : ℝ) * z) * HighGaussianKernel.k186.realProfile.eval z) := by
  intro y z
  have hρ : 0 < gaussianK186FarScale := by norm_num only [gaussianK186FarScale]
  have hy : 0 < y := mul_pos hρ hL
  have he : Real.exp ((z - 5) / 2) = y := by
    simp only [z, add_sub_cancel_left, Real.log_pow, Nat.cast_ofNat,
      mul_div_cancel_left₀ _ (by norm_num only : (2 : ℝ) ≠ 0), Real.exp_log hy]
  have hl : L = Real.exp ((z - 5) / 2) / gaussianK186FarScale := by
    rw [he]
    change L = gaussianK186FarScale * L / gaussianK186FarScale
    rw [mul_comm gaussianK186FarScale L, mul_div_cancel_right₀ _ hρ.ne']
  rw [hl]
  norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  have hs :
    Real.exp ((z - 5) / 2) * Real.exp (-(11 / 4 : ℝ) * z) =
      Real.exp (-(5 / 2 : ℝ)) * Real.exp (-(9 / 4 : ℝ) * z) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  linear_combination (2 / gaussianK186FarScale * HighGaussianKernel.k186.realProfile.eval z) * hs

/-- The negative-profile contribution to reflection is part of the exponentially
damped H30 charge. -/
private theorem k186_reflected_negative_le_h30 (z : ℝ) :
    12 * Real.exp (-z / 2) *
        ((13 / 4 : ℝ) * highNegativeMoment .k186 0 + highNegativeMoment .k186 1) ≤
      Real.exp (-z / 2) * highH30Charge .k186 := by
  have hJ (j : ℕ) : 0 ≤ highNegativeMoment .k186 j := by
    unfold highNegativeMoment
    apply
      intervalIntegral.integral_nonneg
        (by
          norm_num only [profileCorrectionStart, profileCorrectionEnd, Rat.cast_ofNat,
            Int.cast_ofNat])
    intro t _
    exact mul_nonneg (Real.exp_pos _).le (le_max_left _ _)
  have hc :
    12 * ((13 / 4 : ℝ) * highNegativeMoment .k186 0 + highNegativeMoment .k186 1) ≤
      highH30Charge .k186 := by
    unfold highH30Charge
    norm_num only [HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
    linarith only [hJ 0, hJ 1, hJ 2]
  rw [mul_comm (12 : ℝ) (Real.exp (-z / 2)), mul_assoc]
  exact mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)

/-- The negative-profile part of the reflected Euler bound is already included
in the compressed H30 coefficient, so it has one small far-range budget. -/
theorem k186_far_reflected_negative_le {z : ℝ} (hz : 58 ≤ z) (hH : highH30Charge .k186 ≤ 78548) :
    12 * Real.exp (-z / 2) *
        ((13 / 4 : ℝ) * highNegativeMoment .k186 0 + highNegativeMoment .k186 1) ≤
      1 / 10 ^ 6 := by
  have he := high_h30_charge_on_ray .k186 hz hH
  have hg := middle_tail_exp_le 2320 (by decide +kernel)
  norm_num only [Nat.cast_ofNat] at hg
  norm_num only at he
  have hq : (78548 : ℝ) * (1 / middleTailExpDen 2320 : ℚ) ≤ 1 / 10 ^ 6 := by
    have h : (78548 : ℚ) * (1 / middleTailExpDen 2320) ≤ 1 / 10 ^ 6 := by
      unfold middleTailExpDen
      decide +kernel
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr h
  have hm := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 78548)
  nlinarith only [k186_reflected_negative_le_h30 z, he, hm, hq]

/-- The fixed far conductor cap reads only the positive coefficients of the
K186 profile shifted to 58, with the rational monomial weights. -/
noncomputable def k186FarConductorCap : ℝ :=
  let P := HighGaussianKernel.k186.realProfile.comp (Polynomial.X + Polynomial.C 58)
  (2 / gaussianK186FarScale * Real.exp (-(5 / 2 : ℝ))) *
    (Real.exp (-(9 / 4 : ℝ) * 58) *
      ∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 8 : ℝ) * i / (9 / 4)) ^ i)

/-- One fixed coefficient sum controls the entire far conductor reflection. -/
theorem k186_far_conductor_le {L : ℝ} (hL : 10 ^ 12 ≤ L) :
    let z := 5 + Real.log ((gaussianK186FarScale * L) ^ 2)
    2 * L * Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * z) *
        HighGaussianKernel.k186.realProfile.eval z ≤
      k186FarConductorCap := by
  intro z
  have hlog := Real.log_le_log (Real.exp_pos 53) (k186_far_tail_anchor hL)
  rw [Real.log_exp] at hlog
  have hz : 58 ≤ z := by
    change 58 ≤ 5 + Real.log ((gaussianK186FarScale * L) ^ 2)
    linarith only [hlog]
  have hpos := (by norm_num only : (0 : ℝ) < 10 ^ 12).trans_le hL
  rw [k186_reflected_conductor_eq hpos]
  exact
    mul_le_mul_of_nonneg_left
      (decay_poly_le_shifted HighGaussianKernel.k186.realProfile
        (by norm_num only : (0 : ℝ) < 9 / 4) hz)
      (mul_nonneg (by norm_num only [gaussianK186FarScale]) (Real.exp_pos _).le)

/-- The certified K186 conductor coefficient sum gives a far conductor
budget of 200 for every input at or beyond the far anchor. -/
theorem k186_far_conductor_le_200 {L : ℝ} (hL : 10 ^ 12 ≤ L) :
    let z := 5 + Real.log ((gaussianK186FarScale * L) ^ 2)
    2 * L * Real.exp (-(HighGaussianKernel.k186.pole : ℝ) * z) *
        HighGaussianKernel.k186.realProfile.eval z ≤
      200 := by
  refine (k186_far_conductor_le hL).trans ?_
  have hw (i : ℕ) : (3 / 8 : ℝ) * (i : ℝ) / (9 / 4) = (i : ℝ) / 6 := by ring
  unfold k186FarConductorCap
  rw [← mul_assoc, mul_assoc (2 / gaussianK186FarScale), ← Real.exp_add]
  simp only [show -(5 / 2 : ℝ) + -(9 / 4 : ℝ) * 58 = -133 by norm_num only, hw]
  exact k186_conductor_coeff_cap

/-- The two signed reflected moments form one polynomial, whose evaluation
can be shared across the far comparison. -/
noncomputable def k186ReflectedMoment : Polynomial ℝ :=
  Polynomial.C (13 / 4) * eulerMomentPoly HighGaussianKernel.k186.realProfile (9 / 4) +
    eulerMomentPoly HighGaussianKernel.k186.realProfile.derivative (9 / 4)

/-- Recombine the two signed moments without the negative-profile charge. -/
theorem k186_reflected_moment_eval (z : ℝ) :
    k186ReflectedMoment.eval z =
      (13 / 4 : ℝ) * highSignedMoment .k186 0 z + highSignedMoment .k186 1 z := by
  simp only [k186ReflectedMoment, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    euler_moment_poly_eval, eulerPolyMoment, highSignedMoment, Function.iterate_zero,
    Function.iterate_one, id_eq, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat]
  rw [show (11 / 4 : ℝ) - 1 / 2 = 9 / 4 by norm_num only]

/-- At any finite cutoff, the reflected budget is bounded by the signed
moment polynomial and the exponentially damped H30 coefficient. -/
theorem k186_reflected_le_moment {C : ℝ} (z : ℝ) (hC : highH30Charge .k186 ≤ C) :
    highReflectedBudget .k186 z ≤
      6 * Real.exp (-(11 / 4 : ℝ) * z) * k186ReflectedMoment.eval z + Real.exp (-z / 2) * C := by
  have h :=
    (k186_reflected_negative_le_h30 z).trans (mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _))
  simp only [highReflectedBudget, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat,
    show (11 / 4 : ℝ) + 1 / 2 = 13 / 4 by norm_num only, k186_reflected_moment_eval]
  exact add_le_add_right h _

/-- The signed part of the reflected Euler budget uses one upper coefficient
sum at 58, with the remaining negative-profile part handled by H30. -/
noncomputable def k186FarReflectedCap : ℝ :=
  let P := k186ReflectedMoment.comp (Polynomial.X + Polynomial.C 58)
  6 *
    (Real.exp (-(11 / 4 : ℝ) * 58) *
      ∑ i ∈ Finset.range (P.natDegree + 1), max 0 (P.coeff i) * ((3 / 22 : ℝ) * i) ^ i)

/-- The reflected Euler term on the far half-line is bounded by the fixed
signed coefficient sum and the already separated H30 allowance. -/
private theorem k186_far_reflected_le_of_negative {z C : ℝ} (hz : 58 ≤ z)
    (hn :
      12 * Real.exp (-z / 2) *
          ((13 / 4 : ℝ) * highNegativeMoment .k186 0 + highNegativeMoment .k186 1) ≤
        C) :
    highReflectedBudget .k186 z ≤ k186FarReflectedCap + C := by
  have hm := decay_poly_le_shifted k186ReflectedMoment (by norm_num only : (0 : ℝ) < 11 / 4) hz
  have hw (i : ℕ) : (3 / 8 : ℝ) * (i : ℝ) / (11 / 4) = (3 / 22 : ℝ) * i := by ring
  simp only [hw] at hm
  have hc := mul_le_mul_of_nonneg_left hm (by norm_num only : (0 : ℝ) ≤ 6)
  simp only [highReflectedBudget, HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat,
    show (11 / 4 : ℝ) + 1 / 2 = 13 / 4 by norm_num only, ← k186_reflected_moment_eval, mul_assoc]
  exact add_le_add hc (by simpa only [mul_assoc] using hn)

/-- Use the original compressed moment bound from the beginning of the reflected ray. -/
theorem k186_far_reflected_le {z : ℝ} (hz : 58 ≤ z) (hH : highH30Charge .k186 ≤ 78548) :
    highReflectedBudget .k186 z ≤ k186FarReflectedCap + 1 / 10 ^ 6 := by
  exact k186_far_reflected_le_of_negative hz (k186_far_reflected_negative_le hz hH)

/-- The shifted signed moment is precisely the reflected profile obtained
by taking one moment of the rate-weighted input plus its derivative. -/
theorem k186_reflected_moment_shift :
    k186ReflectedMoment.comp (Polynomial.X + Polynomial.C 58) =
      middleReflectionPoly HighGaussianKernel.k186.realProfile (13 / 4) 58 := by
  let B := HighGaussianKernel.k186.realProfile
  let U := Polynomial.C (13 / 4 : ℝ) * B + B.derivative
  have hd : B.derivative.natDegree ≤ B.natDegree :=
    (Polynomial.natDegree_derivative_le B).trans (Nat.sub_le _ _)
  have hC : (Polynomial.C (13 / 4 : ℝ) * B).natDegree ≤ B.natDegree :=
    Polynomial.natDegree_mul_le.trans (by rw [Polynomial.natDegree_C, zero_add])
  have hu : U.natDegree ≤ B.natDegree :=
    (Polynomial.natDegree_add_le_of_le hC hd).trans_eq (max_self _)
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    k186_reflected_moment_eval]
  have heMom (j : ℕ) :
    highSignedMoment .k186 j (t + 58) =
      eulerPolyMoment ((Polynomial.derivative^[j]) B) (t + 58) (9 / 4) := by
    simp only [highSignedMoment, eulerPolyMoment, B, HighGaussianKernel.pole, Rat.cast_div,
      Rat.cast_ofNat, show (11 / 4 : ℝ) - 1 / 2 = 9 / 4 by norm_num only]
  rw [heMom, heMom, Function.iterate_zero, Function.iterate_one, id_eq]
  have hr : (13 / 4 : ℝ) - 1 = 9 / 4 := by norm_num only
  have he : (middleReflectionPoly B (13 / 4) 58).eval t = eulerPolyMoment U (t + 58) (9 / 4) := by
    simpa only [eulerPolyMoment, add_comm (58 : ℝ), hr, U] using
      middle_reflection_poly_eval B (13 / 4) 58 t
  rw [he, euler_moment_eq_row B _ _ B.natDegree _ le_rfl (fun _ _ ↦ rfl),
    euler_moment_eq_row B.derivative _ _ B.natDegree _ hd (fun _ _ ↦ rfl),
    euler_moment_eq_row U _ _ B.natDegree _ hu (fun _ _ ↦ rfl)]
  simp only [U, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]

/-- The reflected Euler budget is at most two millionths on the far
half-line once the compressed H30 coefficient is supplied. -/
theorem k186_far_reflected_le_fixed {z : ℝ} (hz : 58 ≤ z) (hH : highH30Charge .k186 ≤ 78548) :
    highReflectedBudget .k186 z ≤ 2 / 10 ^ 6 := by
  have hc : k186FarReflectedCap ≤ 1 / 10 ^ 6 := by
    unfold k186FarReflectedCap
    rw [k186_reflected_moment_shift]
    exact k186_reflection_coeff_cap
  linarith only [k186_far_reflected_le hz hH, hc]

/-- Beyond 65 the weaker H30 cap suffices to bound the entire reflected cost by two. -/
theorem k186_far_reflected_le_two {z : ℝ} (hz : 65 ≤ z) (hH : highH30Charge .k186 ≤ 10 ^ 12) :
    highReflectedBudget .k186 z ≤ 2 := by
  have he := high_h30_charge_on_ray .k186 hz hH
  have hg := middle_tail_exp_le 2600 (by decide +kernel)
  norm_num only [Nat.cast_ofNat] at hg he
  have hq : (10 ^ 12 : ℝ) * (1 / middleTailExpDen 2600 : ℚ) ≤ 1 := by
    have h : (10 ^ 12 : ℚ) * (1 / middleTailExpDen 2600) ≤ 1 := by
      unfold middleTailExpDen
      decide +kernel
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using
      (Rat.cast_le (K := ℝ)).mpr h
  have hm := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 10 ^ 12)
  have hn :=
    (k186_reflected_negative_le_h30 z).trans
      (show Real.exp (-z / 2) * highH30Charge .k186 ≤ 1 by nlinarith only [he, hm, hq])
  have hc : k186FarReflectedCap ≤ 1 / 10 ^ 6 := by
    unfold k186FarReflectedCap
    rw [k186_reflected_moment_shift]
    exact k186_reflection_coeff_cap
  have hb := k186_far_reflected_le_of_negative ((by norm_num only : (58 : ℝ) ≤ 65).trans hz) hn
  linarith only [hb, hc]

/-- The far comparison uses the verified conductor and right Euler budgets.
The remaining loss hypothesis comprises the common contour, fixed zero mass,
with the certified reflected Euler allowance included. -/
theorem uniform_k186_far_of_reflected_caps {n : ℕ} {α : ℝ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 10 ^ 12 ≤ Real.log n) (hα : 0.7216056623106 ≤ α)
    (hf :
      let y := gaussianK186FarScale * Real.log n
      α * y ≤ k186ForwardValue (y ^ 2))
    (hH : highH30Charge .k186 ≤ 78548)
    (hc :
      let y := gaussianK186FarScale * Real.log n
      3 * highCommonContour .k186 (y ^ 2) - 94173 / 1250 + 3 * HighGaussianKernel.k186.xiMass.re +
          2 / 10 ^ 6 +
          1 / 10 ^ 8 ≤
        61 / 1000 * Real.log y ^ 2 + 300) :
    HasRejectingPrime n (gaussianWitnessCutoff (Real.log n)) := by
  apply uniform_k186_far_of_base_costs hn ho hu hGRH hL hα hf
  dsimp only [k186DirectBaseLoss]
  have hlog := Real.log_le_log (Real.exp_pos 53) (k186_far_tail_anchor hL)
  rw [Real.log_exp] at hlog
  have hz : 58 ≤ 5 + Real.log ((gaussianK186FarScale * Real.log n) ^ 2) := by linarith only [hlog]
  have hcon := k186_far_conductor_le_200 hL
  have href := k186_far_reflected_le_fixed hz hH
  dsimp only at hcon hc
  linarith only [hcon, href, hc]

end PseudoPrime.PrimeTestBounds.MillerRabin
