/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Million
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareRecoveryAbel
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp

/-! # Principal and square-recovery Chebyshev inputs for the affine K131 radius -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem affine_radius_pos {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    0 < gaussianBridgeScale L :=
  (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1

/-- The principal radius squared lies beyond the finite Chebyshev certificate.
This separates the principal RH input from the finite square-recovery input. -/
theorem k131_principal_arg_gt_million {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    1000000 < gaussianBridgeScale L ^ 2 := by
  have h := gaussian_bridge_scale_mem hL
  exact
    (by norm_num only : (1000000 : ℝ) < (465644807 / 400000) ^ 2).trans_le
      (pow_le_pow_left₀ (by norm_num only) h.1 2)

private theorem exp_nine_eighths_le_four : Real.exp (9 / 8 : ℝ) ≤ 4 := by
  rw [show (9 / 8 : ℝ) = 1.125 by norm_num only]
  dyadic_interval [prec := 16]

private theorem recovery_support_bounds {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    17 ≤ y ∧ y ≤ y * Real.exp (9 / 8) ∧ y * Real.exp (9 / 8) ≤ 1000000 := by
  intro y
  have h := gaussian_bridge_scale_mem hL
  refine
    ⟨(by norm_num only : (17 : ℝ) ≤ 465644807 / 400000).trans h.1,
      le_mul_of_one_le_right (affine_radius_pos hL).le (Real.one_le_exp (by norm_num only)), ?_⟩
  exact
    (mul_le_mul h.2 exp_nine_eighths_le_four (Real.exp_pos _).le (by norm_num only)).trans
      (by norm_num only)

/-- Throughout the K131 square-recovery support the normalized psi
error is at most 81/100 by the existing finite certificate. -/
theorem k131_square_recovery_psi {L t : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : t ∈ Set.Icc (gaussianBridgeScale L) (gaussianBridgeScale L * Real.exp (9 / 8))) :
    |Chebyshev.psi t - t| / Real.sqrt t ≤ (81 / 100 : ℝ) := by
  have h := recovery_support_bounds hL
  exact AnalyticNumberTheory.Arithmetic.psi81_million (h.1.trans ht.1) (ht.2.trans h.2.2)

/-- Abel summation on the K131 square-recovery interval, with the lower
endpoint error and the signed square-root density both retained. -/
theorem k131_square_recovery_abel {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (f : ℝ → ℝ) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    (∀ t ∈ Set.Icc y v, DifferentiableAt ℝ f t) →
      ContinuousOn (deriv f) (Set.Icc y v) →
      (∀ t ∈ Set.Icc y v, deriv f t ≤ 0) →
      0 ≤ f y →
      f v = 0 →
      (∫ t in y..v, f t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) -
          2 * (81 / 100) * Real.sqrt y * f y ≤
        ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊, f k * ArithmeticFunction.vonMangoldt k := by
  intro y v hf hd hn hfy hfv
  obtain ⟨hy₁, hyv, hv⟩ := recovery_support_bounds hL
  have hpos (t : ℝ) (ht : t ∈ Set.uIcc y v) : 0 < t := by
    rw [Set.uIcc_of_le hyv] at ht
    exact (affine_radius_pos hL).trans_le ht.1
  have hc : ContinuousOn (deriv f) (Set.uIcc y v) := by rwa [Set.uIcc_of_le hyv]
  have hg (t : ℝ) (ht : t ∈ Set.uIcc y v) :=
    (hasDerivAt_id t).sub ((Real.hasDerivAt_sqrt (hpos t ht).ne').const_mul (81 / 100 : ℝ))
  have hgc : ContinuousOn (fun t : ℝ ↦ 1 - 81 / 100 * (1 / (2 * Real.sqrt t))) (Set.uIcc y v) :=
    fun t ht ↦
    (continuousAt_const.sub
        (continuousAt_const.mul
          (continuousAt_const.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
            (mul_ne_zero (by norm_num only)
              (Real.sqrt_pos.mpr (hpos t ht)).ne')))).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t ht ↦ (hf t (Set.uIcc_of_le hyv ▸ ht)).hasDerivAt) hg hc.intervalIntegrable
      hgc.intervalIntegrable
  change
    (∫ t in y..v, f t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) =
      f v * (v - 81 / 100 * Real.sqrt v) - f y * (y - 81 / 100 * Real.sqrt y) -
        ∫ t in y..v, deriv f t * (t - 81 / 100 * Real.sqrt t) at hi
  rw [hfv, zero_mul] at hi
  have hab := square_recovery_abel_lower hy₁ hyv hv hf hd hn hfy hfv
  linarith only [hi, hab]

/-- The K131 square-recovery weight on the root variable. Its logarithmic
coordinate decreases from 9/4 to zero across the recovery interval. -/
noncomputable def k131RecoveryWeight (y t : ℝ) : ℝ :=
  let v := 9 / 4 - 2 * Real.log (t / y)
  (4 * (gaussianK131Amplitude : ℝ) / t) * Real.exp (-(27 / 16 : ℝ) * v) * gaussianK131Inverse v

private theorem k131_inverse_at_zero : gaussianK131Inverse 0 = 0 := by
  unfold gaussianK131Inverse
  apply Finset.sum_eq_zero
  intro j _
  rw [zero_pow (Nat.ne_of_gt (Nat.zero_lt_succ (2 * j.val + 2))), mul_zero]

/-- The recovery weight evaluated at the lower radius endpoint. -/
theorem k131_recovery_weight_left {y : ℝ} (hy : 0 < y) :
    k131RecoveryWeight y y = 4 * gaussianK131UnitWeight / y := by
  dsimp only [k131RecoveryWeight, gaussianK131UnitWeight]
  rw [div_self hy.ne', Real.log_one, mul_zero, sub_zero]
  ring

/-- The recovery weight vanishes at the upper support endpoint. -/
theorem k131_recovery_weight_right {y : ℝ} (hy : 0 < y) :
    k131RecoveryWeight y (y * Real.exp (9 / 8)) = 0 := by
  unfold k131RecoveryWeight
  dsimp only
  rw [mul_div_cancel_left₀ _ hy.ne', Real.log_exp]
  rw [show (9 / 4 : ℝ) - 2 * (9 / 8) = 0 by norm_num only]
  rw [k131_inverse_at_zero, mul_zero]

private noncomputable def recoveryCoord (y t : ℝ) : ℝ :=
  9 / 4 - 2 * Real.log (t / y)

private theorem recovery_coord_mem {y t : ℝ} (hy : 0 < y)
    (ht : t ∈ Set.Icc y (y * Real.exp (9 / 8))) : recoveryCoord y t ∈ Set.Icc (0 : ℝ) (9 / 4) := by
  have hlo : 1 ≤ t / y := (le_div_iff₀ hy).mpr (by simpa only [one_mul] using ht.1)
  have hhi : t / y ≤ Real.exp (9 / 8) := (div_le_iff₀ hy).mpr (by simpa only [mul_comm] using ht.2)
  have hpos := div_pos (hy.trans_le ht.1) hy
  have hl := Real.log_nonneg hlo
  have hh := (Real.log_le_iff_le_exp hpos).mpr hhi
  unfold recoveryCoord
  exact ⟨by linarith only [hh], by linarith only [hl]⟩

private theorem recovery_weight_eq {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    k131RecoveryWeight y t =
      (4 * (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
        (Real.exp (-(19 / 16 : ℝ) * recoveryCoord y t) *
          gaussianK131Inverse (recoveryCoord y t)) := by
  let v := recoveryCoord y t
  have he : Real.exp ((1 / 2 : ℝ) * v - 9 / 8) = y / t := by
    have hv : (1 / 2 : ℝ) * v - 9 / 8 = -Real.log (t / y) := by
      dsimp only [v, recoveryCoord]
      ring
    rw [hv, Real.exp_neg, Real.exp_log (div_pos ht hy), inv_div]
  have hf : Real.exp (-(27 / 16 : ℝ) * v) = Real.exp (-(19 / 16 : ℝ) * v - 9 / 8) * (t / y) := by
    have hg : -(19 / 16 : ℝ) * v - 9 / 8 = -(27 / 16 : ℝ) * v + ((1 / 2) * v - 9 / 8) := by ring
    rw [hg, Real.exp_add, he]
    field_simp [hy.ne', ht.ne']
  change
    (4 * (gaussianK131Amplitude : ℝ) / t) * Real.exp (-(27 / 16 : ℝ) * v) * gaussianK131Inverse v =
      (4 * (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
        (Real.exp (-(19 / 16 : ℝ) * v) * gaussianK131Inverse v)
  rw [hf, Real.exp_sub]
  rw [Real.exp_neg, div_eq_mul_inv]
  field_simp [hy.ne', ht.ne']

private theorem recovery_coord_deriv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    HasDerivAt (recoveryCoord y) (-(2 / t)) t := by
  have hd := (Real.hasDerivAt_log (div_pos ht hy).ne').comp t ((hasDerivAt_id t).div_const y)
  have h := ((hd.const_mul (2 : ℝ)).const_sub (9 / 4 : ℝ))
  convert h using 1
  · rfl
  · field_simp [hy.ne', ht.ne']

private theorem recovery_coord_left {y : ℝ} (hy : 0 < y) : recoveryCoord y y = 9 / 4 := by
  simp only [recoveryCoord, div_self hy.ne', Real.log_one, mul_zero, sub_zero]

private theorem recovery_coord_right {y : ℝ} (hy : 0 < y) :
    recoveryCoord y (y * Real.exp (9 / 8)) = 0 := by
  simp only [recoveryCoord, mul_div_cancel_left₀ _ hy.ne', Real.log_exp]
  norm_num only

private theorem recovery_coord_spec {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    t = y * Real.exp (9 / 8 - recoveryCoord y t / 2) := by
  have h : (9 / 8 : ℝ) - recoveryCoord y t / 2 = Real.log (t / y) := by
    unfold recoveryCoord
    ring
  rw [h, Real.exp_log (div_pos ht hy), mul_div_cancel₀ _ hy.ne']

private theorem recovery_power_at {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (q : ℝ) :
    t ^ q = y ^ q * Real.exp ((9 / 8 - recoveryCoord y t / 2) * q) := by
  conv_lhs => rw [recovery_coord_spec hy ht]
  rw [Real.mul_rpow hy.le (Real.exp_pos _).le, Real.exp_mul]

private theorem recovery_weight_power {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (q : ℝ) :
    k131RecoveryWeight y t * t ^ q =
      (2 * (gaussianK131Amplitude : ℝ) * y ^ q * Real.exp (9 / 8 * q)) *
        ((Real.exp (-(27 / 16 + q / 2) * recoveryCoord y t) *
            gaussianK131Inverse (recoveryCoord y t)) *
          (2 / t)) := by
  rw [recovery_power_at hy ht]
  let v := recoveryCoord y t
  change
    (4 * (gaussianK131Amplitude : ℝ) / t) * Real.exp (-(27 / 16 : ℝ) * v) * gaussianK131Inverse v *
        (y ^ q * Real.exp ((9 / 8 - v / 2) * q)) =
      _
  have h :
    Real.exp (-(27 / 16 : ℝ) * v) * Real.exp ((9 / 8 - v / 2) * q) =
      Real.exp (9 / 8 * q) * Real.exp (-(27 / 16 + q / 2) * v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ =
        (4 * (gaussianK131Amplitude : ℝ) / t) * gaussianK131Inverse v * y ^ q *
          (Real.exp (-(27 / 16 : ℝ) * v) * Real.exp ((9 / 8 - v / 2) * q)) :=
      by ring
    _ = _ := by
      rw [h]; ring

private theorem recovery_integral_coord {y : ℝ} (hy : 0 < y) (a : ℝ) :
    (∫ t in y..y * Real.exp (9 / 8),
        (Real.exp (-a * recoveryCoord y t) * gaussianK131Inverse (recoveryCoord y t)) * (2 / t)) =
      gaussianK131Moment a := by
  let v := y * Real.exp (9 / 8)
  let g : ℝ → ℝ := fun u ↦ Real.exp (-a * u) * gaussianK131Inverse u
  have hle : y ≤ v := le_mul_of_one_le_right hy.le (Real.one_le_exp (by norm_num only))
  have hpos (t : ℝ) (ht : t ∈ Set.uIcc y v) : 0 < t := by
    rw [Set.uIcc_of_le hle] at ht
    exact hy.trans_le ht.1
  have hd : ContinuousOn (fun t : ℝ ↦ -(2 / t)) (Set.uIcc y v) := fun t ht ↦
    ((continuousAt_const.div continuousAt_id (hpos t ht).ne').neg).continuousWithinAt
  have hB : Continuous gaussianK131Inverse := by
    rw [←
      show gaussianK131InversePoly.eval = gaussianK131Inverse from
        funext gaussian_k131_inverse_eval]
    exact gaussianK131InversePoly.continuous
  have hg : Continuous g := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hB
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (a := y) (b := v) (f := recoveryCoord y) (f' :=
      fun t : ℝ ↦ -(2 / t)) (g := g) (fun t ht ↦ recovery_coord_deriv hy (hpos t ht)) hd
      hg.continuousOn
  rw [recovery_coord_left hy, show recoveryCoord y v = 0 from recovery_coord_right hy,
    intervalIntegral.integral_symm (f := g) 0 (9 / 4)] at h
  simp only [Function.comp_def, mul_neg, intervalIntegral.integral_neg, neg_inj] at h
  exact h

private theorem recovery_power_integral {y : ℝ} (hy : 0 < y) (q : ℝ) :
    (∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t * t ^ q) =
      (2 * (gaussianK131Amplitude : ℝ) * y ^ q * Real.exp (9 / 8 * q)) *
        gaussianK131Moment (27 / 16 + q / 2) := by
  let v := y * Real.exp (9 / 8)
  have hle : y ≤ v := le_mul_of_one_le_right hy.le (Real.one_le_exp (by norm_num only))
  rw [← recovery_integral_coord hy (27 / 16 + q / 2), ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hle] at ht
  exact recovery_weight_power hy (hy.trans_le ht.1) q

private noncomputable def recoveryProfile (v : ℝ) : ℝ :=
  Real.exp (-(19 / 16 : ℝ) * v) * gaussianK131Inverse v

private theorem recovery_profile_deriv (v : ℝ) :
    HasDerivAt recoveryProfile
      (Real.exp (-(19 / 16 : ℝ) * v) *
        (gaussianK131InversePoly.derivative.eval v - (19 / 16) * gaussianK131Inverse v))
      v := by
  have hB : HasDerivAt gaussianK131Inverse (gaussianK131InversePoly.derivative.eval v) v := by
    simpa only [gaussian_k131_inverse_eval] using gaussianK131InversePoly.hasDerivAt v
  have he := ((hasDerivAt_id v).const_mul (-(19 / 16 : ℝ))).exp
  unfold recoveryProfile
  convert he.mul hB using 1
  · rfl
  · simp only [id_eq]
    ring

private theorem recovery_profile_slope {v : ℝ} (hv : v ∈ Set.Icc (0 : ℝ) (9 / 4)) :
    (19 / 16 : ℝ) * gaussianK131Inverse v ≤ gaussianK131InversePoly.derivative.eval v := by
  simp only [gaussianK131Inverse, gaussianK131InversePoly, Polynomial.derivative_sum,
    Polynomial.derivative_monomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let n := 2 * j.val + 3
  have hn : 0 < n := Nat.zero_lt_succ (2 * j.val + 2)
  have hc : 0 ≤ (inverseCoeffs j : ℝ) := by
    have h : ∀ j : Fin 9, 0 ≤ inverseCoeffs j := by decide +kernel
    exact (Rat.cast_nonneg (K := ℝ)).mpr (h j)
  have hn3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.le_add_left 3 (2 * j.val))
  have hp : (19 / 16 : ℝ) * v ≤ (n : ℝ) := by linarith only [hv.2, hn3]
  have he : v ^ n = v ^ (n - 1) * v := by
    nth_rw 1 [← Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
    rw [pow_succ]
  change
    (19 / 16 : ℝ) * ((inverseCoeffs j : ℝ) * v ^ n) ≤
      ((inverseCoeffs j : ℝ) * (n : ℝ)) * v ^ (n - 1)
  rw [he]
  have h := mul_le_mul_of_nonneg_left hp (mul_nonneg hc (pow_nonneg hv.1 (n - 1)))
  linarith only [h]

private noncomputable def recoverySlope (y t : ℝ) : ℝ :=
  let v := recoveryCoord y t
  (4 * (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
    ((Real.exp (-(19 / 16 : ℝ) * v) *
        (gaussianK131InversePoly.derivative.eval v - (19 / 16) * gaussianK131Inverse v)) *
      -(2 / t))

private theorem recovery_weight_deriv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    HasDerivAt (k131RecoveryWeight y) (recoverySlope y t) t := by
  have hd := (recovery_profile_deriv (recoveryCoord y t)).comp t (recovery_coord_deriv hy ht)
  have h := hd.const_mul (4 * (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ)))
  apply h.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds ht] with x hx
  exact recovery_weight_eq hy hx

private theorem recovery_slope_continuous {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    ContinuousAt (recoverySlope y) t := by
  have hv : ContinuousAt (recoveryCoord y) t := (recovery_coord_deriv hy ht).continuousAt
  have hB : ContinuousAt gaussianK131Inverse (recoveryCoord y t) := by
    rw [←
      show gaussianK131InversePoly.eval = gaussianK131Inverse from
        funext gaussian_k131_inverse_eval]
    exact gaussianK131InversePoly.continuous.continuousAt
  have hD : ContinuousAt gaussianK131InversePoly.derivative.eval (recoveryCoord y t) :=
    gaussianK131InversePoly.derivative.continuous.continuousAt
  have he : ContinuousAt (fun u ↦ Real.exp (-(19 / 16 : ℝ) * recoveryCoord y u)) t :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hv)
  have hq : ContinuousAt (fun u : ℝ ↦ -(2 / u)) t :=
    (continuousAt_const.div continuousAt_id ht.ne').neg
  exact
    continuousAt_const.mul
      ((he.mul ((hD.comp hv).sub (continuousAt_const.mul (hB.comp hv)))).mul hq)

private theorem recovery_slope_nonpos {y t : ℝ} (hy : 0 < y)
    (ht : t ∈ Set.Icc y (y * Real.exp (9 / 8))) : recoverySlope y t ≤ 0 := by
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  unfold recoverySlope
  apply
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (div_nonneg (mul_nonneg (by norm_num only) hA) hy.le) (Real.exp_pos _).le)
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.exp_pos _).le
        (sub_nonneg.mpr (recovery_profile_slope (recovery_coord_mem hy ht))))
      (neg_nonpos.mpr (div_nonneg (by norm_num only) (hy.le.trans ht.1)))

private theorem unit_weight_nonneg : 0 ≤ gaussianK131UnitWeight := by
  have h := gaussian_k131_rh_coeff_mem.1
  unfold gaussianK131RhCoeff at h
  have hd : (0 : ℝ) < 2 * (314159 / 100000) := by norm_num only
  simpa only [zero_mul] using (le_div_iff₀ hd).mp h

/-- The specific K131 weight satisfies the finite Abel lower bound.
Only its two explicit integrals remain in the lower bound. -/
theorem k131_recovery_weighted_sum {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    (∫ t in y..v, k131RecoveryWeight y t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) -
        2 * (81 / 100) * Real.sqrt y * (4 * gaussianK131UnitWeight / y) ≤
      ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊, k131RecoveryWeight y k * ArithmeticFunction.vonMangoldt k := by
  intro y v
  have hy : 0 < y := affine_radius_pos hL
  rw [← k131_recovery_weight_left hy]
  apply k131_square_recovery_abel hL
  · intro t ht
    exact (recovery_weight_deriv hy (hy.trans_le ht.1)).differentiableAt
  · apply
      ContinuousOn.congr
        (fun t ht ↦
          (recovery_slope_continuous hy (hy.trans_le (Set.mem_Icc.mp ht).1)).continuousWithinAt)
    exact fun t ht ↦ (recovery_weight_deriv hy (hy.trans_le ht.1)).deriv
  · intro t ht
    rw [(recovery_weight_deriv hy (hy.trans_le ht.1)).deriv]
    exact recovery_slope_nonpos hy ht
  · rw [k131_recovery_weight_left hy]
    exact div_nonneg (mul_nonneg (by norm_num only) unit_weight_nonneg) hy.le
  · exact k131_recovery_weight_right hy

private theorem recovery_moment_main {y : ℝ} (hy : 0 < y) :
    (∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t) =
      2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) := by
  simpa only [Real.rpow_zero, mul_one, mul_zero, Real.exp_zero, zero_div, add_zero] using
    recovery_power_integral hy 0

private theorem recovery_moment_sqrt {y : ℝ} (hy : 0 < y) :
    (∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t * (Real.sqrt t)⁻¹) =
      2 * (gaussianK131Amplitude : ℝ) * (Real.sqrt y)⁻¹ * Real.exp (-(9 / 16 : ℝ)) *
        gaussianK131Moment (23 / 16) := by
  have hle : y ≤ y * Real.exp (9 / 8) :=
    le_mul_of_one_le_right hy.le (Real.one_le_exp (by norm_num only))
  have he :
    (∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t * (Real.sqrt t)⁻¹) =
      ∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t * t ^ (-(1 / 2 : ℝ)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    change k131RecoveryWeight y t * (Real.sqrt t)⁻¹ = k131RecoveryWeight y t * t ^ (-(1 / 2 : ℝ))
    rw [Real.rpow_neg (hy.le.trans ht.1), ← Real.sqrt_eq_rpow]
  rw [he, recovery_power_integral hy, Real.rpow_neg hy.le, ← Real.sqrt_eq_rpow]
  norm_num only

private theorem recovery_integral_split {y : ℝ} (hy : 0 < y) :
    (∫ t in y..y * Real.exp (9 / 8),
        k131RecoveryWeight y t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) =
      (∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t) -
        (81 / 200 : ℝ) *
          ∫ t in y..y * Real.exp (9 / 8), k131RecoveryWeight y t * (Real.sqrt t)⁻¹ := by
  let v := y * Real.exp (9 / 8)
  have hle : y ≤ v := le_mul_of_one_le_right hy.le (Real.one_le_exp (by norm_num only))
  have hp (t : ℝ) (ht : t ∈ Set.uIcc y v) : 0 < t := by
    rw [Set.uIcc_of_le hle] at ht
    exact hy.trans_le ht.1
  have hc : ContinuousOn (k131RecoveryWeight y) (Set.uIcc y v) := fun t ht ↦
    (recovery_weight_deriv hy (hp t ht)).continuousAt.continuousWithinAt
  have hs : ContinuousOn (fun t ↦ (Real.sqrt t)⁻¹) (Set.uIcc y v) := fun t ht ↦
    (Real.continuous_sqrt.continuousAt.inv₀ (Real.sqrt_pos.mpr (hp t ht)).ne').continuousWithinAt
  have hi :
    IntervalIntegrable (fun t ↦ (81 / 200 : ℝ) * (k131RecoveryWeight y t * (Real.sqrt t)⁻¹))
      MeasureTheory.volume y (y * Real.exp (9 / 8)) :=
    (hc.mul hs).intervalIntegrable.const_mul _
  rw [← intervalIntegral.integral_const_mul, ←
    intervalIntegral.integral_sub hc.intervalIntegrable hi]
  apply intervalIntegral.integral_congr
  intro t _
  change
    k131RecoveryWeight y t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t))) =
      k131RecoveryWeight y t - (81 / 200) * (k131RecoveryWeight y t * (Real.sqrt t)⁻¹)
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual finite square-recovery sum is bounded below by the two
bundle constants after evaluating both logarithmic-coordinate integrals. -/
theorem k131_square_recovery_lower {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
        (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y ≤
      ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊, k131RecoveryWeight y k * ArithmeticFunction.vonMangoldt k := by
  intro y v
  have hy : 0 < y := affine_radius_pos hL
  have h := k131_recovery_weighted_sum hL
  change
    (∫ t in y..v, k131RecoveryWeight y t * (1 - 81 / 100 * (1 / (2 * Real.sqrt t)))) -
        2 * (81 / 100) * Real.sqrt y * (4 * gaussianK131UnitWeight / y) ≤
      _ at h
  rw [recovery_integral_split hy, recovery_moment_main hy, recovery_moment_sqrt hy] at h
  refine le_trans ?_ h
  apply le_of_eq
  rw [gaussianK131RecoveryVariation]
  field_simp [(Real.sqrt_pos.mpr hy).ne', hy.ne']
  ring_nf
  rw [Real.sq_sqrt hy.le]
  ring

/-- The normalized principal Chebyshev boundary is bounded below by the
actual principal RH term in the scalar K131 gap. -/
theorem k131_principal_boundary_lower (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    k131PrincipalError gaussianK131RhCoeff y ≤
      -4 * gaussianK131UnitWeight * ((Chebyshev.psi (y ^ 2) - y ^ 2) / y) := by
  intro y
  have hy : 0 < y := affine_radius_pos hL
  have hy₂ : (101 : ℝ) ≤ y ^ 2 :=
    (by norm_num only : (101 : ℝ) ≤ 1000000).trans (k131_principal_arg_gt_million hL).le
  have h := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH hy₂
  rw [Real.sqrt_sq hy.le, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  let v := 2 * Real.log y
  let N := v * (v - Real.log v)
  change |Chebyshev.psi (y ^ 2) - y ^ 2| / y ≤ N / (8 * Real.pi) at h
  have hN : 0 ≤ N := by
    have hw := (div_nonneg (abs_nonneg _) hy.le).trans h
    simpa only [zero_mul] using (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).mp hw
  have hp : (314159 / 100000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hd : (0 : ℝ) < 8 * (314159 / 100000) := by norm_num only
  have hbound :=
    (div_le_div_of_nonneg_right (le_abs_self (Chebyshev.psi (y ^ 2) - y ^ 2)) hy.le).trans
      (h.trans (div_le_div_of_nonneg_left hN hd (mul_le_mul_of_nonneg_left hp (by norm_num only))))
  have hm :=
    mul_le_mul_of_nonpos_left hbound
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num only : (-4 : ℝ) ≤ 0) unit_weight_nonneg)
  refine le_trans ?_ hm
  unfold k131PrincipalError gaussianK131RhCoeff
  change
    -(gaussianK131UnitWeight / (2 * (314159 / 100000))) * N ≤
      -4 * gaussianK131UnitWeight * (N / (8 * (314159 / 100000)))
  apply le_of_eq
  ring

/-- Combine the K131 principal boundary and recovered square contribution.
This is the principal Chebyshev part of the comparison with the scalar gap. -/
theorem k131_principal_recovery_lower (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    k131PrincipalError gaussianK131RhCoeff y +
        (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
          (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) ≤
      -4 * gaussianK131UnitWeight * ((Chebyshev.psi (y ^ 2) - y ^ 2) / y) +
        ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊, k131RecoveryWeight y k * ArithmeticFunction.vonMangoldt k := by
  exact add_le_add (k131_principal_boundary_lower hRH hL) (k131_square_recovery_lower hL)

private theorem recovery_index_le_cutoff {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {k : ℕ}
    (hk : k ≤ ⌊gaussianBridgeScale L * Real.exp (9 / 8)⌋₊) :
    (k : ℝ) ≤ gaussianBridgeScale L ^ 2 := by
  let y := gaussianBridgeScale L
  have hy : 0 < y := affine_radius_pos hL
  have hfour : (4 : ℝ) ≤ y :=
    (by norm_num only : (4 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have hk' := (Nat.le_floor_iff (mul_nonneg hy.le (Real.exp_pos _).le)).mp hk
  have h := mul_le_mul_of_nonneg_left (exp_nine_eighths_le_four.trans hfour) hy.le
  rw [← pow_two] at h
  exact hk'.trans h

private theorem recovery_char_eq_one {q k : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {X : ℝ}
    (hk : (k : ℝ) ≤ X) (hΛ : ArithmeticFunction.vonMangoldt k ≠ 0)
    (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) : χ (k ^ 2 : ℕ) = 1 := by
  obtain ⟨p, j, hp, hj, rfl⟩ :=
    (isPrimePow_nat_iff k).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hp' : p ≤ p ^ j := by
    simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le (Nat.succ_le_of_lt hj))
  have he := hχ p hp ((Nat.cast_le.mpr hp').trans hk)
  simp only [Nat.cast_pow, map_pow, he, one_pow]

/-- On K131 recovery squares, agreement on primes up to the affine cutoff
allows insertion of a character value without changing the weighted sum. -/
theorem k131_recovery_char_sum {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ p = 1) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    (∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊,
        k131RecoveryWeight y k * ArithmeticFunction.vonMangoldt (k ^ 2) * (χ (k ^ 2 : ℕ)).re) =
      ∑ k ∈ Finset.Ioc ⌊y⌋₊ ⌊v⌋₊, k131RecoveryWeight y k * ArithmeticFunction.vonMangoldt k := by
  intro y v
  apply Finset.sum_congr rfl
  intro k hk
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : (2 : ℕ) ≠ 0)]
  by_cases hΛ : ArithmeticFunction.vonMangoldt k = 0
  · simp only [hΛ, mul_zero, zero_mul]
  · rw [recovery_char_eq_one χ (recovery_index_le_cutoff hL (Finset.mem_Ioc.mp hk).2) hΛ hχ,
      Complex.one_re, mul_one]

/-- The forward K131 Mellin weight in the original prime-power variable. -/
noncomputable def k131ForwardWeight (y x : ℝ) : ℝ :=
  let v := 9 / 4 - Real.log (x / y ^ 2)
  ((gaussianK131Amplitude : ℝ) / Real.sqrt x) * Real.exp (-(27 / 16 : ℝ) * v) *
    gaussianK131Inverse v

private theorem recovery_weight_at_square {y t : ℝ} (ht : 0 < t) :
    k131RecoveryWeight y t = 4 * k131ForwardWeight y (t ^ 2) := by
  have hlog : Real.log (t ^ 2 / y ^ 2) = 2 * Real.log (t / y) := by
    rw [← div_pow, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  unfold k131RecoveryWeight k131ForwardWeight
  simp only [Real.sqrt_sq ht.le, hlog]
  ring

/-- Express the finite square recovery in the original prime-power
variable, with the character factor inserted using agreement at the cutoff. -/
theorem k131_recovery_square_sum_lower {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ p = 1) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
        (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y ≤
      ∑ n ∈ (Finset.Ioc ⌊y⌋₊ ⌊v⌋₊).image (fun k : ℕ ↦ k ^ 2),
        4 * k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n * (χ n).re := by
  intro y v
  have hinj : Function.Injective (fun k : ℕ ↦ k ^ 2) := by
    intro a b h
    exact (pow_left_inj₀ (Nat.zero_le a) (Nat.zero_le b) (by decide : (2 : ℕ) ≠ 0)).mp h
  rw [Finset.sum_image (fun _ _ _ _ h ↦ hinj h)]
  refine (k131_square_recovery_lower hL).trans ?_
  apply le_of_eq
  rw [← k131_recovery_char_sum hL χ hχ]
  apply Finset.sum_congr rfl
  intro k hk
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1)
  simp only [Nat.cast_pow, recovery_weight_at_square hk₀]
  rfl

/-- Every recovered square lies strictly above the affine cutoff and at
or below the upper endpoint of the forward kernel support. -/
theorem k131_recovery_square_support {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {n : ℕ}
    (hn :
      n ∈
        (Finset.Ioc ⌊gaussianBridgeScale L⌋₊ ⌊gaussianBridgeScale L * Real.exp (9 / 8)⌋₊).image
          (fun k : ℕ ↦ k ^ 2)) :
    let y := gaussianBridgeScale L
    (n : ℝ) ∈ Set.Ioc (y ^ 2) (y ^ 2 * Real.exp (9 / 4)) := by
  intro y
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hn
  have hy : 0 < y := affine_radius_pos hL
  have hl := (Nat.floor_lt hy.le).mp (Finset.mem_Ioc.mp hk).1
  have hu := (Nat.le_floor_iff (mul_nonneg hy.le (Real.exp_pos _).le)).mp (Finset.mem_Ioc.mp hk).2
  have he : (y * Real.exp (9 / 8)) ^ 2 = y ^ 2 * Real.exp (9 / 4) := by
    rw [mul_pow, ← Real.exp_natCast_mul]
    norm_num only [Nat.cast_ofNat]
  rw [Nat.cast_pow, ← he]
  exact ⟨pow_lt_pow_left₀ hl hy.le (by decide), pow_le_pow_left₀ (Nat.cast_nonneg _) hu 2⟩

/-- The principal boundary and recovered powers in the character sum
jointly dominate the corresponding terms of the K131 comparison. -/
theorem k131_boundary_square_lower (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ p = 1) :
    let y := gaussianBridgeScale L
    let v := y * Real.exp (9 / 8)
    k131PrincipalError gaussianK131RhCoeff y +
        (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
          (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) ≤
      -4 * gaussianK131UnitWeight * ((Chebyshev.psi (y ^ 2) - y ^ 2) / y) +
        ∑ n ∈ (Finset.Ioc ⌊y⌋₊ ⌊v⌋₊).image (fun k : ℕ ↦ k ^ 2),
          4 * k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n * (χ n).re := by
  exact add_le_add (k131_principal_boundary_lower hRH hL) (k131_recovery_square_sum_lower hL χ hχ)

end PseudoPrime.PrimeTestBounds.MillerRabin
