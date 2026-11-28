/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131PsiBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeroIntegralBound
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants2
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincTailAnchorRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroConjugateSum
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCount100RH
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131PsiBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-! # Prime support of the K131 forward trace deficit -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem exp_forward_le : Real.exp (9 / 4 : ℝ) ≤ 16 := by
  rw [show (9 / 4 : ℝ) = 9 / 8 + 9 / 8 by norm_num only, Real.exp_add]
  exact
    (mul_le_mul exp_nine_eighths_le_four exp_nine_eighths_le_four (Real.exp_pos _).le
          (by norm_num only)).trans
      (by norm_num only)

private theorem forward_weight_sqrt {y x : ℝ} (hx : 0 < x) :
    k131ForwardWeight y x = k131RecoveryWeight y (Real.sqrt x) / 4 := by
  have h := recovery_weight_at_square (y := y) (Real.sqrt_pos.mpr hx)
  rw [Real.sq_sqrt hx.le] at h
  linarith only [h]

private theorem forward_weight_deriv {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    HasDerivAt (k131ForwardWeight y) (recoverySlope y (Real.sqrt x) * (1 / (2 * Real.sqrt x)) / 4)
      x := by
  have hd :=
    ((recovery_weight_deriv hy (Real.sqrt_pos.mpr hx)).comp x
          (Real.hasDerivAt_sqrt hx.ne')).div_const
      (4 : ℝ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx] with u hu
  exact forward_weight_sqrt hu

private theorem forward_slope_continuous {y x : ℝ} (hy : 0 < y) (hx : 0 < x) :
    ContinuousAt (deriv (k131ForwardWeight y)) x := by
  have hs : ContinuousAt (fun u ↦ recoverySlope y (Real.sqrt u)) x :=
    (recovery_slope_continuous hy (Real.sqrt_pos.mpr hx)).comp Real.continuous_sqrt.continuousAt
  have hi : ContinuousAt (fun u ↦ 1 / (2 * Real.sqrt u)) x :=
    continuousAt_const.div (continuousAt_const.mul Real.continuous_sqrt.continuousAt)
      (mul_ne_zero (by norm_num only) (Real.sqrt_pos.mpr hx).ne')
  apply ((hs.mul hi).div_const 4).congr
  filter_upwards [lt_mem_nhds hx] with u hu
  exact (forward_weight_deriv hy hu).deriv.symm

private theorem forward_support_square (y : ℝ) :
    (y * Real.exp (9 / 8)) ^ 2 = y ^ 2 * Real.exp (9 / 4) := by
  rw [mul_pow, ← Real.exp_natCast_mul]
  norm_num only [Nat.cast_ofNat]

private theorem forward_slope_nonpos {y x : ℝ} (hy : 0 < y)
    (hx : x ∈ Set.Icc (y ^ 2) (y ^ 2 * Real.exp (9 / 4))) : deriv (k131ForwardWeight y) x ≤ 0 := by
  have hp := (pow_pos hy 2).trans_le hx.1
  have hs : Real.sqrt x ∈ Set.Icc y (y * Real.exp (9 / 8)) := by
    refine ⟨Real.le_sqrt_of_sq_le hx.1, ?_⟩
    have h := Real.sqrt_le_sqrt hx.2
    rw [← forward_support_square, Real.sqrt_sq (mul_nonneg hy.le (Real.exp_pos _).le)] at h
    exact h
  rw [(forward_weight_deriv hy hp).deriv]
  exact
    div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (recovery_slope_nonpos hy hs)
        (div_nonneg zero_le_one (mul_nonneg (by norm_num only) (Real.sqrt_nonneg _))))
      (by norm_num only)

private theorem forward_weight_left {y : ℝ} (hy : 0 < y) :
    k131ForwardWeight y (y ^ 2) = gaussianK131UnitWeight / y := by
  rw [forward_weight_sqrt (pow_pos hy 2), Real.sqrt_sq hy.le, k131_recovery_weight_left hy]
  ring

private theorem forward_weight_right {y : ℝ} (hy : 0 < y) :
    k131ForwardWeight y (y ^ 2 * Real.exp (9 / 4)) = 0 := by
  rw [forward_weight_sqrt (mul_pos (pow_pos hy 2) (Real.exp_pos _)), ← forward_support_square,
    Real.sqrt_sq (mul_nonneg hy.le (Real.exp_pos _).le), k131_recovery_weight_right hy, zero_div]

/-- Exact Abel formula for the prime terms of the K131 forward deficit.
The weight vanishes at the right endpoint. -/
theorem k131_prime_tail_abel {y : ℝ} (hy : 0 < y) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊,
        if n.Prime then k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n else 0) =
      -(gaussianK131UnitWeight / y * Chebyshev.theta x) -
        ∫ t in x..u, deriv (k131ForwardWeight y) t * Chebyshev.theta t := by
  intro x u
  let g : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n else 0
  have hx : 0 < x := pow_pos hy 2
  have hxu : x ≤ u := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hc : ContinuousOn (deriv (k131ForwardWeight y)) (Set.Icc x u) := fun t ht ↦
    (forward_slope_continuous hy (hx.trans_le ht.1)).continuousWithinAt
  have hprefix (t : ℝ) : ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, g n = Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have h :=
    sum_mul_eq_sub_sub_integral_mul g hx.le hxu
      (fun t ht ↦ (forward_weight_deriv hy (hx.trans_le ht.1)).differentiableAt) hc.integrableOn_Icc
  simp only [hprefix, show k131ForwardWeight y u = 0 from forward_weight_right hy,
    show k131ForwardWeight y x = gaussianK131UnitWeight / y from forward_weight_left hy, zero_mul,
    zero_sub] at h
  rw [← intervalIntegral.integral_of_le hxu] at h
  refine (Finset.sum_congr rfl ?_).trans h
  intro n _
  by_cases hp : n.Prime
  · simp only [hp, ite_true, g, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp only [g, hp, ite_false, mul_zero]

/-- The Mangoldt tail, with its principal boundary canceled, equals the
forward mass and a signed Chebyshev error integral. -/
theorem k131_centered_forward_abel {y : ℝ} (hy : 0 < y) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x) =
      (∫ t in x..u, f t) - ∫ t in x..u, deriv f t * (Chebyshev.psi t - t) := by
  intro x u f
  have hx : 0 < x := pow_pos hy 2
  have hxu : x ≤ u := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hf (t : ℝ) (ht : t ∈ Set.Icc x u) : DifferentiableAt ℝ f t :=
    (forward_weight_deriv hy (hx.trans_le ht.1)).differentiableAt
  have hc : ContinuousOn (deriv f) (Set.Icc x u) := fun t ht ↦
    (forward_slope_continuous hy (hx.trans_le ht.1)).continuousWithinAt
  have hd : ContinuousOn (deriv f) (Set.uIcc x u) := by rwa [Set.uIcc_of_le hxu]
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt hx.le hxu hf hc.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc, show f u = 0 from forward_weight_right hy,
    show f x = gaussianK131UnitWeight / y from forward_weight_left hy, zero_mul, zero_sub] at h
  rw [← intervalIntegral.integral_of_le hxu] at h
  have hi :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (fun t ht ↦ (hf t (Set.uIcc_of_le hxu ▸ ht)).hasDerivAt) (fun t _ ↦ hasDerivAt_id t)
      hd.intervalIntegrable (continuous_const.intervalIntegrable x u)
  simp only [id_eq, mul_one, show f u = 0 from forward_weight_right hy, zero_mul, zero_sub,
    show f x = gaussianK131UnitWeight / y from forward_weight_left hy] at hi
  have hm := (Chebyshev.psi_mono.intervalIntegrable (μ := MeasureTheory.volume)).continuousOn_mul hd
  have ht : IntervalIntegrable (fun t ↦ deriv f t * t) MeasureTheory.volume x u :=
    (hd.mul continuous_id.continuousOn).intervalIntegrable
  rw [show
      (fun t ↦ deriv f t * (Chebyshev.psi t - t)) = fun t ↦
        deriv f t * Chebyshev.psi t - deriv f t * t
      by
      funext t; exact mul_sub ..,
    intervalIntegral.integral_sub hm ht]
  linarith only [h, hi]

/-- The forward smooth mass is the rate-35/16 moment after the
square-root substitution. -/
theorem k131_forward_mass {y : ℝ} (hy : 0 < y) :
    (∫ t in y ^ 2..y ^ 2 * Real.exp (9 / 4), k131ForwardWeight y t) =
      (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * gaussianK131Moment (35 / 16) := by
  let v := y * Real.exp (9 / 8)
  have hle : y ≤ v := le_mul_of_one_le_right hy.le (Real.one_le_exp (by norm_num only))
  have hfc : ContinuousOn (k131ForwardWeight y) ((fun t : ℝ ↦ t ^ 2) '' Set.uIcc y v) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hle] at ht
    exact (forward_weight_deriv hy (pow_pos (hy.trans_le ht.1) 2)).continuousAt.continuousWithinAt
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (a := y) (b := v) (f := fun t : ℝ ↦ t ^ 2) (f' :=
      fun t ↦ 2 * t)
      (fun t _ ↦ by
        have hid : (id : ℝ → ℝ) ^ 2 = fun z ↦ z ^ 2 := rfl
        simpa only [hid, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq] using
          (hasDerivAt_id t).pow 2)
      (continuous_const.mul continuous_id).continuousOn hfc
  rw [forward_support_square] at h
  rw [← h]
  have hm := recovery_power_integral hy 1
  norm_num only [Real.rpow_one, mul_one] at hm
  have he :
    (∫ t in y..v, k131ForwardWeight y (t ^ 2) * (2 * t)) =
      (1 / 2 : ℝ) * ∫ t in y..v, k131RecoveryWeight y t * t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    change k131ForwardWeight y (t ^ 2) * (2 * t) = (1 / 2 : ℝ) * (k131RecoveryWeight y t * t)
    rw [recovery_weight_at_square (hy.trans_le ht.1)]
    ring
  change (∫ t in y..v, k131ForwardWeight y (t ^ 2) * (2 * t)) = _
  rw [he, hm]
  ring

/-- Under RH, the centered forward tail is bounded by its exact smooth mass plus
the integral of the Lee–Nosal error against the nonnegative variation weight. -/
theorem k131_centered_forward_upper (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y)
    (hx101 : 101 ≤ y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x) ≤
      (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * gaussianK131Moment (35 / 16) +
        ∫ t in x..u,
          -deriv f t *
            (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi) * Real.sqrt t) := by
  intro x u f
  have hx : 0 < x := pow_pos hy 2
  have hxu : x ≤ u := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hpos (t : ℝ) (ht : t ∈ Set.uIcc x u) : 1 < t :=
    (by norm_num only : (1 : ℝ) < 101).trans_le (hx101.trans (Set.uIcc_of_le hxu ▸ ht).1)
  have hd : ContinuousOn (fun t ↦ -deriv f t) (Set.uIcc x u) := fun t ht ↦
    (forward_slope_continuous hy (zero_lt_one.trans (hpos t ht))).neg.continuousWithinAt
  have hl : ContinuousOn Real.log (Set.uIcc x u) := fun t ht ↦
    (Real.continuousAt_log (zero_lt_one.trans (hpos t ht)).ne').continuousWithinAt
  have hll : ContinuousOn (fun t ↦ Real.log (Real.log t)) (Set.uIcc x u) := fun t ht ↦
    ((Real.continuousAt_log (Real.log_pos (hpos t ht)).ne').comp
        (Real.continuousAt_log (zero_lt_one.trans (hpos t ht)).ne')).continuousWithinAt
  have hc := ((hl.mul (hl.sub hll)).div_const (8 * Real.pi)).mul Real.continuous_sqrt.continuousOn
  have he : IntervalIntegrable (fun t ↦ Chebyshev.psi t - t) MeasureTheory.volume x u :=
    Chebyshev.psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable x u)
  rw [k131_centered_forward_abel hy, k131_forward_mass hy]
  apply add_le_add_right
  rw [← intervalIntegral.integral_neg]
  apply
    intervalIntegral.integral_mono_on hxu ((he.continuousOn_mul hd).congr (fun t _ ↦ neg_mul _ _))
      (hd.mul hc).intervalIntegrable
  intro t ht
  have hs := Real.sqrt_pos.mpr (hx.trans_le ht.1)
  have hb :=
    (div_le_iff₀ hs).mp (AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH (hx101.trans ht.1))
  rw [← neg_mul]
  exact
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans hb)
      (neg_nonneg.mpr (forward_slope_nonpos hy ht))

private theorem forward_power_base_le {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p k : ℕ}
    (hp : p.Prime) (hk : 2 ≤ k) (hpk : (p : ℝ) ^ k ≤ gaussianBridgeScale L ^ 2 * Real.exp (9 / 4)) :
    (p : ℝ) ≤ gaussianBridgeScale L ^ 2 := by
  let y := gaussianBridgeScale L
  have hy : 0 < y := affine_radius_pos hL
  have hfour : (4 : ℝ) ≤ y :=
    (by norm_num only : (4 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have h16 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 4) hfour 2
  have hyexp : Real.exp (9 / 4 : ℝ) ≤ y ^ 2 :=
    exp_forward_le.trans (by simpa only [show (4 : ℝ) ^ 2 = 16 by norm_num only] using h16)
  have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (Nat.one_le_cast.mpr hp.one_lt.le) hk
  exact
    (pow_le_pow_iff_left₀ (Nat.cast_nonneg p) (sq_nonneg y) (by decide : (2 : ℕ) ≠ 0)).mp
      (hpow.trans
        (hpk.trans
          (by
            rw [pow_two (y ^ 2)]
            exact mul_le_mul_of_nonneg_left hyexp (sq_nonneg y))))

private theorem forward_weight_nonneg {y x : ℝ} (hy : 0 < y) (hx : 0 < x)
    (hu : x ≤ y ^ 2 * Real.exp (9 / 4)) : 0 ≤ k131ForwardWeight y x := by
  have hz :=
    (Real.log_le_iff_le_exp (div_pos hx (pow_pos hy 2))).mpr
      ((div_le_iff₀ (pow_pos hy 2)).mpr (by simpa only [mul_comm] using hu))
  have ha : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  unfold k131ForwardWeight
  exact
    mul_nonneg (mul_nonneg (div_nonneg ha (Real.sqrt_nonneg _)) (Real.exp_pos _).le)
      (inverse_nonneg (sub_nonneg.mpr hz))

private theorem recovered_square_not_prime {n : ℕ} {S : Finset ℕ}
    (hn : n ∈ S.image (fun k : ℕ ↦ k ^ 2)) : ¬n.Prime := by
  obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hn
  exact Nat.Prime.not_prime_pow le_rfl

/-- The recovered squares and the forward primes occupy disjoint parts of
the Mangoldt tail, so their combined mass is at most the full tail. -/
theorem k131_prime_square_tail_le {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let S := Finset.Ioc ⌊y ^ 2⌋₊ ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    let w := fun n : ℕ ↦ k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n
    (∑ n ∈ S, if n.Prime then w n else 0) + (∑ n ∈ U, w n) ≤ ∑ n ∈ S, w n := by
  intro y S U w
  have hy : 0 < y := affine_radius_pos hL
  have hu : U ⊆ S := by
    intro n hn
    have hn' := k131_recovery_square_support hL hn
    exact
      Finset.mem_Ioc.mpr
        ⟨(Nat.floor_lt (sq_nonneg y)).mpr hn'.1,
          (Nat.le_floor_iff (mul_nonneg (sq_nonneg y) (Real.exp_pos _).le)).mpr hn'.2⟩
  have hfilter : S.filter (fun n ↦ n ∈ U) = U := by
    ext n
    exact Finset.mem_filter.trans ⟨And.right, fun hn ↦ ⟨hu hn, hn⟩⟩
  rw [← hfilter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hp : n.Prime
  · have hnu : n ∉ U := fun hm ↦ recovered_square_not_prime hm hp
    simp only [hp, hnu, ite_true, ite_false, add_zero, le_refl]
  by_cases hnu : n ∈ U
  · simp only [hp, hnu, ite_true, ite_false, zero_add, le_refl]
  have hl := (Nat.floor_lt (sq_nonneg y)).mp (Finset.mem_Ioc.mp hn).1
  have hr :=
    (Nat.le_floor_iff (mul_nonneg (sq_nonneg y) (Real.exp_pos _).le)).mp (Finset.mem_Ioc.mp hn).2
  simp only [hp, hnu, ite_false, zero_add]
  exact
    mul_nonneg (forward_weight_nonneg hy ((sq_nonneg y).trans_lt hl) hr)
      ArithmeticFunction.vonMangoldt_nonneg

/-- The RH upper bound for the centered forward prime tail retains a
separate subtraction for the Mangoldt mass on the recovered squares. -/
theorem k131_centered_prime_upper (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊, if n.Prime then f n * ArithmeticFunction.vonMangoldt n else 0) +
        (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x) +
        (∑ n ∈ U, f n * ArithmeticFunction.vonMangoldt n) ≤
      (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * gaussianK131Moment (35 / 16) +
        ∫ t in x..u,
          -deriv f t *
            (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi) * Real.sqrt t) := by
  intro y x u f U
  have h := k131_prime_square_tail_le hL
  have h101 : (101 : ℝ) ≤ y ^ 2 :=
    (by norm_num only : (101 : ℝ) ≤ 1000000).trans (k131_principal_arg_gt_million hL).le
  have hu := k131_centered_forward_upper hRH (affine_radius_pos hL) h101
  simpa only [add_right_comm] using (add_le_add_left h _).trans hu

private theorem forward_nonprime_one {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {q n : ℕ}
    (χ : DirichletCharacter ℂ q) (hn : ¬n.Prime)
    (hu : (n : ℝ) ≤ gaussianBridgeScale L ^ 2 * Real.exp (9 / 4))
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0)
    (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ p = 1) : χ n = 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hk₂ : 2 ≤ k :=
    Nat.succ_le_of_lt
      (lt_of_le_of_ne (Nat.succ_le_of_lt hk) (fun h ↦ hn (by simpa only [← h, pow_one] using hp)))
  rw [Nat.cast_pow] at hu
  simp only [Nat.cast_pow, map_pow, hχ p hp (forward_power_base_le hL hp hk₂ hu), one_pow]

/-- In the K131 forward support, proper prime powers contribute zero
to the deficit when all three characters agree on primes through the cutoff.
Only the prime terms require the four-fold weight bound. -/
theorem k131_forward_deficit_le {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p q r : ℕ}
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let S := Finset.Ioc ⌊y ^ 2⌋₊ ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    (∑ n ∈ S,
        (3 - ((a n).re + (b n).re + (c n).re)) *
          (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n)) ≤
      ∑ n ∈ S,
        if n.Prime then 4 * (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) else 0 := by
  intro y S
  apply Finset.sum_le_sum
  intro n hn
  have hy : 0 < y := affine_radius_pos hL
  have hu :=
    (Nat.le_floor_iff (mul_nonneg (sq_nonneg y) (Real.exp_pos _).le)).mp (Finset.mem_Ioc.mp hn).2
  have hl := (Nat.floor_lt (sq_nonneg y)).mp (Finset.mem_Ioc.mp hn).1
  by_cases hn' : n.Prime
  · rw [ite_eq_left hn']
    exact
      mul_le_mul_of_nonneg_right (by linarith only [ht n])
        (mul_nonneg (forward_weight_nonneg hy ((sq_nonneg y).trans_lt hl) hu)
          ArithmeticFunction.vonMangoldt_nonneg)
  rw [ite_eq_right hn']
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, le_refl]
  rw [forward_nonprime_one hL a hn' hu hΛ ha, forward_nonprime_one hL b hn' hu hΛ hb,
    forward_nonprime_one hL c hn' hu hΛ hc, Complex.one_re]
  norm_num only [zero_mul]

/-- Above the cutoff, the character trace dominates minus the full Mangoldt
tail plus four times the recovered square mass. This is the forward part
of the raw Euler lower bound used before the principal explicit formula. -/
theorem k131_forward_trace_lower {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p q r : ℕ}
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let S := Finset.Ioc ⌊y ^ 2⌋₊ ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    let w := fun n : ℕ ↦ k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n
    (-(∑ n ∈ S, w n) + 4 * (∑ n ∈ U, w n)) ≤ (∑ n ∈ S, ((a n).re + (b n).re + (c n).re) * w n) := by
  intro y S U w
  have hd := k131_forward_deficit_le hL a b c ht ha hb hc
  have hs := k131_prime_square_tail_le hL
  have he (n : ℕ) : (if n.Prime then 4 * w n else 0) = 4 * (if n.Prime then w n else 0) := by
    rw [mul_ite, mul_zero]
  change
    (∑ n ∈ S, (3 - ((a n).re + (b n).re + (c n).re)) * w n) ≤
      (∑ n ∈ S, if n.Prime then 4 * w n else 0) at hd
  simp only [he, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum] at hd
  dsimp only [y, S, U, w] at hd ⊢
  linarith only [hd, hs]

private theorem prefix_char_one {q n : ℕ} (χ : DirichletCharacter ℂ q) {X : ℝ} (hn : (n : ℝ) ≤ X)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) (hχ : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    χ n = 1 := by
  obtain ⟨p, j, hp, hj, rfl⟩ :=
    (isPrimePow_nat_iff n).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpow : p ≤ p ^ j := by
    simpa only [pow_one] using (pow_le_pow_right₀ hp.one_lt.le (Nat.succ_le_of_lt hj))
  simp only [Nat.cast_pow, map_pow, hχ p hp ((Nat.cast_le.mpr hpow).trans hn), one_pow]

private theorem sum_prefix_tail {x u : ℕ} (hxu : x ≤ u) (w : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 0 u, w n) = (∑ n ∈ Finset.Icc 0 x, w n) + (∑ n ∈ Finset.Ioc x u, w n) := by
  have hd : Disjoint (Finset.Icc 0 x) (Finset.Ioc x u) :=
    Finset.disjoint_left.mpr fun _ ha hb ↦
      (not_lt_of_ge (Finset.mem_Icc.mp ha).2) (Finset.mem_Ioc.mp hb).1
  have he : Finset.Icc 0 x ∪ Finset.Ioc x u = Finset.Icc 0 u := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc, Nat.zero_le, true_and]
    exact
      ⟨fun h ↦ h.elim (fun hx ↦ hx.trans hxu) And.right, fun hu ↦
        (le_or_gt n x).imp_right (fun hx ↦ ⟨hx, hu⟩)⟩
  rw [← Finset.sum_union hd, he]

private theorem k131_log_mangoldt_integral {t : ℝ} (ht : 1 ≤ t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t =
      ∫ v in (1 : ℝ)..t, Chebyshev.psi v / v := by
  have hp (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) t) : 0 < v := zero_lt_one.trans_le hv.1
  have hd : ContinuousOn (deriv Real.log) (Set.Icc 1 t) := by
    rw [show deriv Real.log = fun v ↦ v⁻¹ from funext Real.deriv_log]
    exact continuousOn_id.inv₀ (fun v hv ↦ (hp v hv).ne')
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt
      (show (0 : ℝ) ≤ 1 from zero_le_one) ht
      (fun v hv ↦ (Real.hasDerivAt_log (hp v hv).ne').differentiableAt) hd.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [Real.log_one, zero_mul, sub_zero, Nat.floor_one, ← intervalIntegral.integral_of_le ht] at h
  simp only [Real.deriv_log] at h
  have hm : (1 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  have hs :
    (∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, Real.log n * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 1 ⌊t⌋₊, Real.log n * ArithmeticFunction.vonMangoldt n := by
    have he := sum_prefix_tail hm (fun n ↦ Real.log n * ArithmeticFunction.vonMangoldt n)
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)] at he
    have hsmall : Finset.Icc (0 : ℕ) 1 = {0, 1} := by decide
    simpa only [hsmall, Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)),
      Finset.sum_singleton, ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one,
      mul_zero, zero_add, add_zero] using he
  have hf :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t =
      Real.log t * Chebyshev.psi t -
        ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, Real.log n * ArithmeticFunction.vonMangoldt n := by
    rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum,
      AnalyticNumberTheory.Arithmetic.psi_eq_positive_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm,
      Real.log_div (zero_lt_one.trans_le ht).ne' (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1).ne']
    ring
  rw [hf, hs, h, sub_sub_cancel]
  apply intervalIntegral.integral_congr
  intro v _
  change v⁻¹ * Chebyshev.psi v = Chebyshev.psi v / v
  rw [div_eq_mul_inv, mul_comm]

private theorem k131_log_psi_parts {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {P : ℝ → ℝ}
    (hP : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ P t) (hD : ContinuousOn (deriv P) (Set.Icc a b)) :
    let M := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    (∫ t in a..b, P t * (Chebyshev.psi t / t)) =
      P b * M b - P a * M a - ∫ t in a..b, deriv P t * M t := by
  intro M
  let g := fun t ↦ Chebyshev.psi t / t
  let G := fun t ↦ ∫ v in (1 : ℝ)..t, g v
  have hi : IntervalIntegrable g MeasureTheory.volume 1 b := by
    have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹) (Set.uIcc 1 b) := by
      rw [Set.uIcc_of_le (ha.trans hab)]
      exact continuousOn_id.inv₀ (fun t ht ↦ (zero_lt_one.trans_le ht.1).ne')
    simpa only [g, div_eq_mul_inv, mul_comm] using
      (Chebyshev.psi_mono.intervalIntegrable (a := 1) (b := b) (μ :=
            MeasureTheory.volume)).continuousOn_mul
        hc
  have hG : AbsolutelyContinuousOnInterval G a b := by
    apply (hi.absolutelyContinuousOnInterval_intervalIntegral Set.left_mem_uIcc).mono
    rw [Set.uIcc_of_le (ha.trans hab), Set.uIcc_of_le hab]
    exact Set.Icc_subset_Icc_left ha
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hLip : LipschitzOnWith ⟨max C 0, le_max_right _ _⟩ P (Set.Icc a b) :=
    Convex.lipschitzOnWith_of_nnNorm_deriv_le hP
      (fun t ht ↦ NNReal.coe_le_coe.mp ((hC t ht).trans (le_max_left _ _))) (convex_Icc _ _)
  have hPac : AbsolutelyContinuousOnInterval P a b :=
    LipschitzOnWith.absolutelyContinuousOnInterval (Set.uIcc_of_le hab ▸ hLip)
  have he (t : ℝ) (ht : 1 ≤ t) : G t = M t := (k131_log_mangoldt_integral ht).symm
  have h := hPac.integral_mul_deriv_eq_deriv_mul hG
  rw [he b (ha.trans hab), he a ha] at h
  have heI : (∫ t in a..b, deriv P t * G t) = ∫ t in a..b, deriv P t * M t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change deriv P t * G t = deriv P t * M t
    rw [he t (ha.trans (Set.uIcc_of_le hab ▸ ht).1)]
  rw [← heI, ← h]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hi.ae_hasDerivAt_integral] with t ht ht'
  have htb := Set.uIoc_of_le hab ▸ ht'
  have htI : t ∈ Set.uIcc (1 : ℝ) b := by
    rw [Set.uIcc_of_le (ha.trans hab)]
    exact ⟨ha.trans htb.1.le, htb.2⟩
  change P t * g t = P t * deriv G t
  rw [(ht htI 1 (Set.left_mem_uIcc)).deriv]

private theorem forward_log_slope_smooth {y : ℝ} (hy : 0 < y) :
    ContDiffOn ℝ 1 (fun t ↦ t * deriv (k131ForwardWeight y) t) (Set.Ioi 0) := by
  have hf : ContDiffOn ℝ 2 (k131ForwardWeight y) (Set.Ioi 0) := by
    intro t ht
    have hpos : 0 < t := ht
    have hs : ContDiffAt ℝ 2 Real.sqrt t := Real.contDiffAt_sqrt hpos.ne'
    have hd : ContDiffAt ℝ 2 (fun z : ℝ ↦ z / y ^ 2) t := contDiffAt_id.div_const _
    have hl := (Real.contDiffAt_log.mpr (div_pos hpos (pow_pos hy 2)).ne').comp t hd
    have hv' : ContDiffAt ℝ 2 (fun z : ℝ ↦ 9 / 4 - Real.log (z / y ^ 2)) t :=
      contDiffAt_const.sub hl
    have hi : ContDiffAt ℝ 2 (fun z ↦ gaussianK131Inverse (9 / 4 - Real.log (z / y ^ 2))) t := by
      unfold gaussianK131Inverse
      exact ContDiffAt.sum (fun j _ ↦ contDiffAt_const.mul (hv'.pow (2 * j.val + 3)))
    have he :
      ContDiffAt ℝ 2 (fun z ↦ Real.exp (-(27 / 16 : ℝ) * (9 / 4 - Real.log (z / y ^ 2)))) t :=
      (contDiffAt_const.mul hv').exp
    have hA : ContDiffAt ℝ 2 (fun z ↦ (gaussianK131Amplitude : ℝ) / Real.sqrt z) t :=
      contDiffAt_const.div hs (Real.sqrt_pos.mpr hpos).ne'
    have hf' :
      k131ForwardWeight y = fun z ↦
        ((gaussianK131Amplitude : ℝ) / Real.sqrt z) *
          Real.exp (-(27 / 16 : ℝ) * (9 / 4 - Real.log (z / y ^ 2))) *
          gaussianK131Inverse (9 / 4 - Real.log (z / y ^ 2)) :=
      rfl
    rw [hf']
    exact ((hA.mul he).mul hi).contDiffWithinAt
  exact contDiffOn_id.mul (hf.deriv_of_isOpen isOpen_Ioi (by decide))

private theorem k131_prefix_abel {y t : ℝ} (hy : 0 < y) (ht : 1 ≤ t) :
    (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) =
      k131ForwardWeight y t * Chebyshev.psi t -
        ∫ v in (1 : ℝ)..t, deriv (k131ForwardWeight y) v * Chebyshev.psi v := by
  let f := k131ForwardWeight y
  have hp (v : ℝ) (hv : v ∈ Set.Icc (1 : ℝ) t) : 0 < v := zero_lt_one.trans_le hv.1
  have hd : ContinuousOn (deriv f) (Set.Icc 1 t) := fun v hv ↦
    (forward_slope_continuous hy (hp v hv)).continuousWithinAt
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt
      (show (0 : ℝ) ≤ 1 from zero_le_one) ht
      (fun v hv ↦ (forward_weight_deriv hy (hp v hv)).differentiableAt) hd.integrableOn_Icc
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [Chebyshev.psi_one, mul_zero, sub_zero, Nat.floor_one] at h
  rw [← intervalIntegral.integral_of_le ht] at h
  have hm : (1 : ℕ) ≤ ⌊t⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using ht)
  rw [sum_prefix_tail hm]
  have hsmall : Finset.Icc (0 : ℕ) 1 = {0, 1} := by decide
  simpa only [hsmall, Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)),
    Finset.sum_singleton, ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one,
    mul_zero, add_zero, zero_add] using h

/-- The first Abel transform of the principal combination retains the exact
boundary at the cutoff. The range below 1 contributes no Mangoldt mass. -/
theorem k131_principal_abel {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let w := fun n : ℕ ↦ f n * ArithmeticFunction.vonMangoldt n
    4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) =
      4 * (gaussianK131UnitWeight / y) * Chebyshev.psi x -
          3 * (∫ t in (1 : ℝ)..x, deriv f t * Chebyshev.psi t) +
        ∫ t in x..u, deriv f t * Chebyshev.psi t := by
  intro x u f w
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  change
    (4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * ArithmeticFunction.vonMangoldt n) -
        (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n)) =
      _
  rw [k131_prefix_abel hy hx, k131_prefix_abel hy (hx.trans hxu), forward_weight_left hy,
    forward_weight_right hy]
  have hi {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ deriv f t * Chebyshev.psi t) MeasureTheory.volume a b := by
    have hc : ContinuousOn (deriv f) (Set.uIcc a b) := by
      rw [Set.uIcc_of_le hab]
      exact fun t ht ↦
        (forward_slope_continuous hy (zero_lt_one.trans_le (ha.trans ht.1))).continuousWithinAt
    exact Chebyshev.psi_mono.intervalIntegrable.continuousOn_mul hc
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hx) (hi hx hxu)]
  ring

private theorem forward_slope_right {y : ℝ} (hy : 0 < y) :
    deriv (k131ForwardWeight y) (y ^ 2 * Real.exp (9 / 4)) = 0 := by
  have hB : gaussianK131InversePoly.derivative.eval 0 = 0 := by
    simp only [gaussianK131InversePoly, Polynomial.derivative_sum, Polynomial.derivative_monomial,
      Polynomial.eval_finsetSum, Polynomial.eval_monomial]
    apply Finset.sum_eq_zero
    intro j _
    have hn : 2 * j.val + 3 - 1 ≠ 0 :=
      Nat.ne_of_gt
        (Nat.sub_pos_of_lt (lt_of_lt_of_le (by decide : 1 < 3) (Nat.le_add_left 3 (2 * j.val))))
    rw [zero_pow hn, mul_zero]
  rw [(forward_weight_deriv hy (mul_pos (pow_pos hy 2) (Real.exp_pos _))).deriv, ←
    forward_support_square, Real.sqrt_sq (mul_nonneg hy.le (Real.exp_pos _).le)]
  simp only [recoverySlope, recovery_coord_right hy, k131_inverse_at_zero, hB, mul_zero, sub_zero,
    zero_mul, zero_div]

/-- The second Abel transform replaces both Chebyshev integrals in the
principal combination by logarithmically weighted Mangoldt integrals. -/
theorem k131_principal_second_abel {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let w := fun n : ℕ ↦ f n * ArithmeticFunction.vonMangoldt n
    let P := fun t ↦ t * deriv f t
    let M := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
    4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) =
      4 * (gaussianK131UnitWeight / y) * Chebyshev.psi x - 4 * P x * M x +
          3 * (∫ t in (1 : ℝ)..x, deriv P t * M t) -
        ∫ t in x..u, deriv P t * M t := by
  intro x u f w P M
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hp {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, deriv f t * Chebyshev.psi t) =
      P b * M b - P a * M a - ∫ t in a..b, deriv P t * M t := by
    have hmem (t : ℝ) (ht : t ∈ Set.Icc a b) : t ∈ Set.Ioi (0 : ℝ) :=
      zero_lt_one.trans_le (ha.trans ht.1)
    have hd0 : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
    rw [←
      k131_log_psi_parts ha hab
        (fun t ht ↦
          ((hs.differentiableOn (by decide)) t (hmem t ht)).differentiableAt
            (isOpen_Ioi.mem_nhds (hmem t ht)))
        (hd0.continuousOn.mono hmem)]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := hmem t (Set.uIcc_of_le hab ▸ ht)
    change deriv f t * Chebyshev.psi t = (t * deriv f t) * (Chebyshev.psi t / t)
    field_simp [(show 0 < t from ht').ne']
  rw [k131_principal_abel hy hx, hp le_rfl hx, hp hx hxu]
  have hm : M 1 = 0 := by
    change AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 1 = 0
    rw [k131_log_mangoldt_integral le_rfl, intervalIntegral.integral_same]
  have hu : P u = 0 := by
    change u * deriv (k131ForwardWeight y) (y ^ 2 * Real.exp (9 / 4)) = 0
    rw [forward_slope_right hy, mul_zero]
  rw [hm, hu]
  ring

/-- Reversed logarithmic coordinate of the forward weight at radius `y`. -/
noncomputable def forwardCoord (y t : ℝ) : ℝ :=
  9 / 4 - Real.log (t / y ^ 2)

private theorem forward_coord_deriv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    HasDerivAt (forwardCoord y) (-t⁻¹) t := by
  have hd := ((hasDerivAt_id t).div_const (y ^ 2)).log (div_pos ht (pow_pos hy 2)).ne'
  have h := (hasDerivAt_const t (9 / 4 : ℝ)).sub hd
  convert h using 1
  · rfl
  · simp only [id_eq, zero_sub]
    field_simp [hy.ne', ht.ne']

private theorem forward_weight_coord {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    k131ForwardWeight y t =
      ((gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8)) *
        ((Real.exp (-(35 / 16 : ℝ) * forwardCoord y t) * gaussianK131Inverse (forwardCoord y t)) *
          t⁻¹) := by
  let v := forwardCoord y t
  have he : Real.exp (9 / 4 - v) = t / y ^ 2 := by
    rw [show 9 / 4 - v = Real.log (t / y ^ 2) by
        unfold v forwardCoord; ring,
      Real.exp_log (div_pos ht (pow_pos hy 2))]
  have hs : (y * Real.exp (9 / 8 - v / 2)) ^ 2 = t := by
    rw [mul_pow, ← Real.exp_natCast_mul]
    norm_num only [Nat.cast_ofNat]
    rw [show 2 * (9 / 8 - v / 2) = 9 / 4 - v by ring, he]
    field_simp [hy.ne']
  have hr : y * Real.exp (9 / 8 - v / 2) = Real.sqrt t := by
    rw [← hs, Real.sqrt_sq (mul_nonneg hy.le (Real.exp_pos _).le)]
  have hexp :
    Real.exp (9 / 8 - v / 2) * Real.exp (-(27 / 16 : ℝ) * v) =
      Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * v) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change
    ((gaussianK131Amplitude : ℝ) / Real.sqrt t) * Real.exp (-(27 / 16 : ℝ) * v) *
        gaussianK131Inverse v =
      _
  rw [div_eq_mul_inv,
    show (Real.sqrt t)⁻¹ = Real.sqrt t * t⁻¹
      by
      field_simp [(Real.sqrt_pos.mpr ht).ne', ht.ne']
      rw [Real.sq_sqrt ht.le],
    ← hr]
  calc
    _ =
        ((gaussianK131Amplitude : ℝ) * y) *
          (Real.exp (9 / 8 - v / 2) * Real.exp (-(27 / 16 : ℝ) * v)) *
          gaussianK131Inverse v *
          t⁻¹ :=
      by ring
    _ = _ := by
      rw [hexp]; change _ = _ * (Real.exp (-(35 / 16 : ℝ) * v) * _ * _); ring

/-- The smooth mass over a positive interval is a finite exponential moment
of the inverse Mellin polynomial, with reversed logarithmic endpoints. -/
theorem k131_mass_log_interval {y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, k131ForwardWeight y t) =
      ((gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8)) *
        ∫ v in forwardCoord y b..forwardCoord y a,
          Real.exp (-(35 / 16 : ℝ) * v) * gaussianK131Inverse v := by
  let g := fun v ↦ Real.exp (-(35 / 16 : ℝ) * v) * gaussianK131Inverse v
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := ha.trans_le (Set.uIcc_of_le hab ▸ ht).1
  have hd : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Set.uIcc a b) :=
    (continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')).neg
  have hB : Continuous gaussianK131Inverse := by
    rw [←
      show gaussianK131InversePoly.eval = gaussianK131Inverse from
        funext gaussian_k131_inverse_eval]
    exact gaussianK131InversePoly.continuous
  have hg : Continuous g := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hB
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b) (f := forwardCoord y) (f' := fun t ↦
      -t⁻¹) (g := g) (fun t ht ↦ forward_coord_deriv hy (hp t ht)) hd hg.continuousOn
  rw [intervalIntegral.integral_symm (f := g) (forwardCoord y b) (forwardCoord y a)] at h
  simp only [Function.comp_def, mul_neg, intervalIntegral.integral_neg, neg_inj] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  exact forward_weight_coord hy (hp t ht)

/-- The smooth prefix-minus-tail combination has the same rate on both
sides of the cutoff. The lower endpoint 1 maps to `9/4 + 2 log y`. -/
theorem k131_principal_mass {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) :
    let f := k131ForwardWeight y
    let g := fun v ↦ Real.exp (-(35 / 16 : ℝ) * v) * gaussianK131Inverse v
    3 * (∫ t in (1 : ℝ)..y ^ 2, f t) - (∫ t in y ^ 2..y ^ 2 * Real.exp (9 / 4), f t) =
      ((gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8)) *
        (3 * (∫ v in (9 / 4 : ℝ)..9 / 4 + 2 * Real.log y, g v) - gaussianK131Moment (35 / 16)) := by
  intro f g
  have hcut : forwardCoord y (y ^ 2) = 9 / 4 := by
    unfold forwardCoord
    rw [div_self (pow_pos hy 2).ne', Real.log_one, sub_zero]
  have hone : forwardCoord y 1 = 9 / 4 + 2 * Real.log y := by
    unfold forwardCoord
    rw [one_div, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  change
    3 * (∫ t in (1 : ℝ)..y ^ 2, k131ForwardWeight y t) -
        (∫ t in y ^ 2..y ^ 2 * Real.exp (9 / 4), k131ForwardWeight y t) =
      _
  rw [k131_mass_log_interval hy zero_lt_one hx, k131_forward_mass hy, hcut, hone]
  ring

/-- The exponential antiderivative polynomial, formed by a finite sum of
iterated derivatives. It applies to both real and complex rates. -/
noncomputable def k131AntiPoly {F : Type*} [Field F] (P : Polynomial F) (s : F) : Polynomial F :=
  ∑ j ∈ Finset.range 20, Polynomial.C ((s ^ (j + 1))⁻¹) * (Polynomial.derivative^[j]) P

private theorem moment_poly_deriv {F : Type*} [Field F] {P : Polynomial F} (hP : P.natDegree < 20)
    {s : F} (hs : s ≠ 0) (t : F) :
    (k131AntiPoly P s).derivative.eval t - s * (k131AntiPoly P s).eval t = -P.eval t := by
  let d := fun j ↦ ((Polynomial.derivative^[j]) P).eval t
  have hzero : d 20 = 0 := by
    change ((Polynomial.derivative^[20]) P).eval t = 0
    rw [Polynomial.iterate_derivative_eq_zero hP, Polynomial.eval_zero]
  have hshift (j : ℕ) : (((Polynomial.derivative^[j]) P).derivative).eval t = d (j + 1) := by
    change _ = ((Polynomial.derivative^[j + 1]) P).eval t
    rw [Function.iterate_succ_apply']
  have hfactor (j : ℕ) : s * ((s ^ (j + 1))⁻¹ * d j) = (s ^ j)⁻¹ * d j := by
    rw [pow_succ, mul_inv]
    field_simp [hs, pow_ne_zero j hs]
  simp only [k131AntiPoly, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, hshift]
  change
    (∑ j ∈ Finset.range 20, (s ^ (j + 1))⁻¹ * d (j + 1)) -
        s * (∑ j ∈ Finset.range 20, (s ^ (j + 1))⁻¹ * d j) =
      -P.eval t
  rw [Finset.mul_sum]
  simp only [hfactor]
  let A := fun j ↦ (s ^ j)⁻¹ * d j
  change (∑ j ∈ Finset.range (19 + 1), A (j + 1)) - (∑ j ∈ Finset.range (19 + 1), A j) = -P.eval t
  rw [Finset.sum_range_succ (fun j ↦ A (j + 1)) 19, Finset.sum_range_succ' A 19]
  have h19 : A (19 + 1) = 0 := by simp only [A, hzero, mul_zero]
  have h0 : A 0 = P.eval t := by
    simp only [A, d, pow_zero, inv_one, one_mul, Function.iterate_zero_apply]
  rw [h19, h0]
  ring

private theorem real_anti_poly (P : Polynomial ℝ) (s : ℝ) :
    k131MomentPoly P s 0 = k131AntiPoly P s := by
  have hc (j : ℕ) : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  simp only [k131MomentPoly, k131AntiPoly, add_zero, div_self (hc _), one_div]

/-- The existing finite derivative polynomial evaluates the exponential
integral exactly as the difference of its two endpoint values. -/
theorem k131_exp_poly_integral {P : Polynomial ℝ} (hP : P.natDegree < 20) {s : ℝ} (hs : s ≠ 0)
    (a b : ℝ) :
    (∫ t in a..b, Real.exp (-s * t) * P.eval t) =
      Real.exp (-s * a) * (k131MomentPoly P s 0).eval a -
        Real.exp (-s * b) * (k131MomentPoly P s 0).eval b := by
  let Q := k131MomentPoly P s 0
  have hd (t : ℝ) :
    HasDerivAt (fun v ↦ -(Real.exp (-s * v) * Q.eval v)) (Real.exp (-s * t) * P.eval t) t := by
    have he := ((hasDerivAt_id t).const_mul (-s)).exp
    have h := (he.mul (Q.hasDerivAt t)).neg
    convert h using 1
    · rfl
    · simp only [id_eq]
      have hn := moment_poly_deriv hP hs t
      rw [← real_anti_poly] at hn
      change Q.derivative.eval t - s * Q.eval t = -P.eval t at hn
      nlinarith only [congrArg (fun z ↦ Real.exp (-s * t) * z) hn]
  have hc : Continuous (fun t ↦ Real.exp (-s * t) * P.eval t) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hc.intervalIntegrable a b)
  exact
    h.trans
      (by
        dsimp only [Q]; ring)

/-- Evaluate the real projection of a complex exponential polynomial
by the same finite antiderivative at the two real endpoints. -/
theorem k131_complex_exp_integral {P : Polynomial ℂ} (hP : P.natDegree < 20) {s : ℂ} (hs : s ≠ 0)
    (c : ℂ) (a b : ℝ) :
    (∫ t in a..b, (c * Complex.exp (-s * (t : ℂ)) * P.eval (t : ℂ)).re) =
      (c * Complex.exp (-s * (a : ℂ)) * (k131AntiPoly P s).eval (a : ℂ) -
          c * Complex.exp (-s * (b : ℂ)) * (k131AntiPoly P s).eval (b : ℂ)).re := by
  let Q := k131AntiPoly P s
  have hd (t : ℝ) :
    HasDerivAt (fun v : ℝ ↦ (-(c * Complex.exp (-s * (v : ℂ)) * Q.eval (v : ℂ))).re)
      (c * Complex.exp (-s * (t : ℂ)) * P.eval (t : ℂ)).re t := by
    have he := (((hasDerivAt_id (t : ℂ)).const_mul (-s)).cexp).const_mul c
    have h := (he.mul (Q.hasDerivAt (t : ℂ))).neg
    have h' :
      HasDerivAt (fun v : ℂ ↦ -(c * Complex.exp (-s * v) * Q.eval v))
        (c * Complex.exp (-s * (t : ℂ)) * P.eval (t : ℂ)) (t : ℂ) := by
      convert h using 1
      · rfl
      · simp only [id_eq]
        have hn := moment_poly_deriv hP hs (t : ℂ)
        change Q.derivative.eval (t : ℂ) - s * Q.eval (t : ℂ) = -P.eval (t : ℂ) at hn
        linear_combination c * Complex.exp (-s * (t : ℂ)) * hn
    exact h'.real_of_complex
  have hc : Continuous (fun t : ℝ ↦ (c * Complex.exp (-s * (t : ℂ)) * P.eval (t : ℂ)).re) :=
    Complex.continuous_re.comp
      ((continuous_const.mul
            (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).mul
        (P.continuous.comp Complex.continuous_ofReal))
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hc.intervalIntegrable a b)
  exact
    h.trans
      (by
        simp only [Complex.neg_re, Complex.sub_re, Q]; ring)

private theorem forward_inverse_degree : gaussianK131InversePoly.natDegree < 20 := by
  apply Nat.lt_succ_of_le
  unfold gaussianK131InversePoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact
    (Polynomial.natDegree_monomial_le _).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt)) 3)

/-- The principal linear coefficient from the raw K131 inverse Mellin
profile. Its two values are moments at the cutoff and at the support edge. -/
noncomputable def k131PrincipalDelta : ℝ :=
  let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
  (gaussianK131Amplitude : ℝ) * Real.exp (9 / 8) *
    (4 * Real.exp (-(35 / 16 : ℝ) * (9 / 4)) * Q.eval (9 / 4) - Q.eval 0)

/-- The smooth principal mass is the linear main term minus the exact
exponential correction for truncating its left endpoint at 1. -/
theorem k131_principal_mass_eval {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) :
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
    3 * (∫ t in (1 : ℝ)..y ^ 2, f t) - (∫ t in y ^ 2..y ^ 2 * Real.exp (9 / 4), f t) =
      k131PrincipalDelta * y -
        3 * (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) *
          Q.eval z := by
  intro z f Q
  rw [k131_principal_mass hy hx]
  unfold gaussianK131Moment
  simp only [← gaussian_k131_inverse_eval]
  rw [k131_exp_poly_integral forward_inverse_degree (by norm_num only : (35 / 16 : ℝ) ≠ 0),
    k131_exp_poly_integral forward_inverse_degree (by norm_num only : (35 / 16 : ℝ) ≠ 0)]
  dsimp only [k131PrincipalDelta, z, Q]
  simp only [mul_zero, Real.exp_zero, one_mul]
  ring

private theorem forward_weight_profile {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    k131ForwardWeight y t =
      ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
        recoveryProfile (forwardCoord y t) := by
  have hs := Real.sqrt_pos.mpr ht
  have hc : recoveryCoord y (Real.sqrt t) = forwardCoord y t := by
    unfold recoveryCoord forwardCoord
    have hh := Real.log_pow (Real.sqrt t / y) 2
    rw [div_pow, Real.sq_sqrt ht.le] at hh
    norm_num only [Nat.cast_ofNat] at hh
    rw [hh]
  rw [forward_weight_sqrt ht, recovery_weight_eq hy hs, hc]
  unfold recoveryProfile
  ring

private theorem forward_log_slope_eval {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let v := forwardCoord y t
    t * deriv (k131ForwardWeight y) t =
      K *
        (Real.exp (-(19 / 16 : ℝ) * v) *
          ((19 / 16 : ℝ) * gaussianK131Inverse v - gaussianK131InversePoly.derivative.eval v)) := by
  intro K v
  have hd := ((recovery_profile_deriv v).comp t (forward_coord_deriv hy ht)).const_mul K
  have hf :=
    hd.congr_of_eventuallyEq (f₁ := k131ForwardWeight y)
      (by
        filter_upwards [lt_mem_nhds ht] with u hu
        exact forward_weight_profile hy hu)
  rw [hf.deriv]
  field_simp [ht.ne']
  ring

private theorem log_second_profile_deriv (v : ℝ) :
    HasDerivAt
      (fun z ↦
        Real.exp (-(19 / 16 : ℝ) * z) *
          ((19 / 16 : ℝ) * gaussianK131Inverse z - gaussianK131InversePoly.derivative.eval z))
      (-(Real.exp (-(19 / 16 : ℝ) * v) *
          (((19 / 16 : ℝ) ^ 2) * gaussianK131Inverse v -
              (2 * (19 / 16 : ℝ)) * gaussianK131InversePoly.derivative.eval v +
            gaussianK131InversePoly.derivative.derivative.eval v)))
      v := by
  have hB : HasDerivAt gaussianK131Inverse (gaussianK131InversePoly.derivative.eval v) v := by
    simpa only [gaussian_k131_inverse_eval] using gaussianK131InversePoly.hasDerivAt v
  have h :=
    (((hasDerivAt_id v).const_mul (-(19 / 16 : ℝ))).exp).mul
      ((hB.const_mul (19 / 16 : ℝ)).sub (gaussianK131InversePoly.derivative.hasDerivAt v))
  convert h using 1
  · rfl
  · simp only [id_eq, Pi.sub_apply]
    ring

/-- The derivative of the logarithmic slope is the weighted polynomial
`d² B - 2 d B' + B''` used in the principal remainder, with `d = 19/16`. -/
theorem k131_log_slope_deriv {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    let v := forwardCoord y t
    deriv (fun u ↦ u * deriv (k131ForwardWeight y) u) t =
      ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
          (Real.exp (-(19 / 16 : ℝ) * v) *
            (((19 / 16 : ℝ) ^ 2) * gaussianK131Inverse v -
                (2 * (19 / 16 : ℝ)) * gaussianK131InversePoly.derivative.eval v +
              gaussianK131InversePoly.derivative.derivative.eval v)) /
        t := by
  intro v
  let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
  have hd := ((log_second_profile_deriv v).comp t (forward_coord_deriv hy ht)).const_mul K
  have hf :=
    hd.congr_of_eventuallyEq (f₁ := fun u ↦ u * deriv (k131ForwardWeight y) u)
      (by
        filter_upwards [lt_mem_nhds ht] with u hu
        exact forward_log_slope_eval hy hu)
  rw [hf.deriv]
  simp only [v, K, neg_mul_neg, div_eq_mul_inv, mul_assoc]

private theorem forward_inverse_coeff_nonneg (n : ℕ) : 0 ≤ gaussianK131InversePoly.coeff n := by
  rw [gaussianK131InversePoly, Polynomial.finsetSum_coeff]
  apply Finset.sum_nonneg
  intro j _
  rw [Polynomial.coeff_monomial]
  simp only [Finsupp.single_apply]
  split
  · exact Rat.cast_nonneg.mpr ((show ∀ k : Fin 9, 0 ≤ inverseCoeffs k by decide +kernel) j)
  · exact le_rfl

private theorem forward_eval_nonneg {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n) {v : ℝ}
    (hv : 0 ≤ v) : 0 ≤ P.eval v := by
  rw [Polynomial.eval_eq_sum_range]
  exact Finset.sum_nonneg fun n _ ↦ mul_nonneg (hP n) (pow_nonneg hv n)

private theorem forward_deriv_coeff_nonneg {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n) (n : ℕ) :
    0 ≤ P.derivative.coeff n := by
  rw [Polynomial.coeff_derivative]
  exact mul_nonneg (hP _) (add_nonneg (Nat.cast_nonneg n) zero_le_one)

/-- On the forward support, replacing the minus sign in the polynomial
for the second logarithmic derivative bounds its absolute value. -/
theorem k131_abs_log_slope_deriv {y t : ℝ} (hy : 0 < y) (ht : 0 < t)
    (hu : t ≤ y ^ 2 * Real.exp (9 / 4)) :
    let v := forwardCoord y t
    |deriv (fun u ↦ u * deriv (k131ForwardWeight y) u) t| ≤
      ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
          (Real.exp (-(19 / 16 : ℝ) * v) *
            (((19 / 16 : ℝ) ^ 2) * gaussianK131Inverse v +
              (2 * (19 / 16 : ℝ)) * gaussianK131InversePoly.derivative.eval v +
              gaussianK131InversePoly.derivative.derivative.eval v)) /
        t := by
  intro v
  have hv : 0 ≤ v :=
    sub_nonneg.mpr
      ((Real.log_le_iff_le_exp (div_pos ht (pow_pos hy 2))).mpr
        ((div_le_iff₀ (pow_pos hy 2)).mpr (by simpa only [mul_comm] using hu)))
  have hB := inverse_nonneg hv
  have hD := forward_eval_nonneg (forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg) hv
  have hDD :=
    forward_eval_nonneg
      (forward_deriv_coeff_nonneg (forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg)) hv
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hK := mul_nonneg (div_nonneg hA hy.le) (Real.exp_pos (-(9 / 8 : ℝ))).le
  rw [k131_log_slope_deriv hy ht, abs_div, abs_mul, abs_of_nonneg hK, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_of_pos ht]
  apply div_le_div_of_nonneg_right _ ht.le
  apply mul_le_mul_of_nonneg_left _ hK
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact abs_le.mpr ⟨by linarith only [hB, hDD], by linarith only [hD]⟩

/-- In the centered principal error above 1, subtracting the nontrivial
zero series and the constant leaves exactly the negative trivial-zero series. -/
theorem k131_centered_trivial_part {t : ℝ} (ht : 1 < t) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
          Real.log (2 * Real.pi) * Real.log t +
          AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
        (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re =
      -AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t := by
  rw [AnalyticNumberTheory.RiemannZeta.log_weighted_exact ht]
  ring

private theorem k131_trivial_decay {t : ℝ} (ht : 1 < t) :
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t ≤
      (5 / 12 : ℝ) * t⁻¹ ^ 2 := by
  have hπ : Real.pi ^ 2 / 24 ≤ (5 / 12 : ℝ) := by
    have h := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_d20.le 2
    norm_num only at h
    linarith only [h]
  exact
    (AnalyticNumberTheory.RiemannZeta.triv_decay ht).trans
      (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hπ (sq_nonneg t⁻¹))

/-- The cutoff contribution from the trivial zeros is bounded by the
inverse-fifth-power loss already present in the K131 scalar gap. -/
theorem k131_trivial_edge_le {y : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2) :
    let P := fun t ↦ t * deriv (k131ForwardWeight y) t
    |4 * P (y ^ 2) * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries (y ^ 2)| ≤
      gaussianK131EdgeLoss / y ^ 5 := by
  intro P
  have hz : forwardCoord y (y ^ 2) = 9 / 4 := by
    unfold forwardCoord
    rw [div_self (pow_pos hy 2).ne', Real.log_one, sub_zero]
  have hs := forward_log_slope_eval hy (pow_pos hy 2)
  dsimp only at hs
  rw [hz] at hs
  change
    |4 * (y ^ 2 * deriv (k131ForwardWeight y) (y ^ 2)) *
          AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries (y ^ 2)| ≤
      _
  rw [hs, abs_mul, abs_of_nonneg (AnalyticNumberTheory.RiemannZeta.triv_nonneg hx)]
  refine (mul_le_mul_of_nonneg_left (k131_trivial_decay hx) (abs_nonneg _)).trans_eq ?_
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg (div_nonneg hA hy.le),
    abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 4)]
  unfold gaussianK131EdgeLoss
  rw [show -(27 / 16 : ℝ) * (9 / 4) = -(9 / 8) + -(19 / 16 : ℝ) * (9 / 4) by norm_num only,
    Real.exp_add]
  field_simp [hy.ne']
  ring

/-- For `t > 1` in the support, the trivial-zero integrand is bounded by
the positive derivative envelope with two additional inverse powers of `t`. -/
theorem k131_trivial_integrand_le {y t : ℝ} (hy : 0 < y) (ht : 1 < t)
    (hu : t ≤ y ^ 2 * Real.exp (9 / 4)) :
    let v := forwardCoord y t
    let P := fun u ↦ u * deriv (k131ForwardWeight y) u
    |deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t| ≤
      (((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
            (Real.exp (-(19 / 16 : ℝ) * v) *
              (((19 / 16 : ℝ) ^ 2) * gaussianK131Inverse v +
                (2 * (19 / 16 : ℝ)) * gaussianK131InversePoly.derivative.eval v +
                gaussianK131InversePoly.derivative.derivative.eval v)) /
          t) *
        ((5 / 12 : ℝ) * t⁻¹ ^ 2) := by
  intro v P
  rw [abs_mul, abs_of_nonneg (AnalyticNumberTheory.RiemannZeta.triv_nonneg ht)]
  exact
    mul_le_mul (k131_abs_log_slope_deriv hy (zero_lt_one.trans ht) hu) (k131_trivial_decay ht)
      (AnalyticNumberTheory.RiemannZeta.triv_nonneg ht)
      ((abs_nonneg _).trans (k131_abs_log_slope_deriv hy (zero_lt_one.trans ht) hu))

/-- The polynomial with positive coefficients that majorizes the absolute
second logarithmic derivative in the principal remainder. -/
noncomputable def k131RemainderPoly : Polynomial ℝ :=
  let B := gaussianK131InversePoly
  Polynomial.C ((19 / 16 : ℝ) ^ 2) * B + Polynomial.C (2 * (19 / 16 : ℝ)) * B.derivative +
    B.derivative.derivative

private theorem forward_eval_mono {P : Polynomial ℝ} (hP : ∀ n, 0 ≤ P.coeff n) {v z : ℝ}
    (hv : 0 ≤ v) (hvz : v ≤ z) : P.eval v ≤ P.eval z := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv hvz n) (hP n)

private theorem remainder_poly_coeff (n : ℕ) : 0 ≤ k131RemainderPoly.coeff n := by
  simp only [k131RemainderPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul]
  exact
    add_nonneg
      (add_nonneg (mul_nonneg (sq_nonneg _) (forward_inverse_coeff_nonneg n))
        (mul_nonneg (by norm_num only) (forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg n)))
      (forward_deriv_coeff_nonneg (forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg) n)

private theorem forward_coord_pos_le {y t : ℝ} (hy : 0 < y) (ht : 1 ≤ t)
    (hu : t ≤ y ^ 2 * Real.exp (9 / 4)) :
    forwardCoord y t ∈ Set.Icc 0 (9 / 4 + 2 * Real.log y) := by
  have hp : 0 < t := zero_lt_one.trans_le ht
  refine
    ⟨sub_nonneg.mpr
        ((Real.log_le_iff_le_exp (div_pos hp (pow_pos hy 2))).mpr
          ((div_le_iff₀ (pow_pos hy 2)).mpr (by simpa only [mul_comm] using hu))),
      ?_⟩
  unfold forwardCoord
  rw [Real.log_div hp.ne' (pow_pos hy 2).ne', Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [Real.log_nonneg ht]

private theorem forward_decay_power {y t : ℝ} (hy : 0 < y) (ht : 0 < t) :
    ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
        Real.exp (-(19 / 16 : ℝ) * forwardCoord y t) =
      k131Prefactor * y ^ (-(27 / 8 : ℝ)) * t ^ (19 / 16 : ℝ) := by
  unfold forwardCoord k131Prefactor
  rw [Real.log_div ht.ne' (pow_pos hy 2).ne', Real.log_pow, Real.rpow_def_of_pos hy,
    Real.rpow_def_of_pos ht]
  norm_num only [Nat.cast_ofNat]
  have he :
    Real.exp (-(19 / 16 : ℝ) * (9 / 4 - (Real.log t - 2 * Real.log y))) =
      Real.exp (-(19 / 16 : ℝ) * (9 / 4)) *
        (Real.exp (Real.log t * (19 / 16 : ℝ)) * Real.exp (Real.log y * (-(19 / 8 : ℝ)))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he, show -(243 / 64 : ℝ) = -(9 / 8) + -(19 / 16 : ℝ) * (9 / 4) by norm_num only, Real.exp_add]
  have hyexp :
    Real.exp (Real.log y * (-(27 / 8 : ℝ))) = Real.exp (Real.log y * (-(19 / 8 : ℝ))) / y := by
    calc
      _ = Real.exp (Real.log y * (-(19 / 8 : ℝ)) - Real.log y) := by
        congr 1; ring
      _ = _ := by rw [Real.exp_sub, Real.exp_log hy]
  rw [hyexp]
  ring

private theorem trivial_integrand_power {y t : ℝ} (hy : 0 < y) (ht : 1 < t)
    (hu : t ≤ y ^ 2 * Real.exp (9 / 4)) :
    let z := 9 / 4 + 2 * Real.log y
    let P := fun u ↦ u * deriv (k131ForwardWeight y) u
    |deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t| ≤
      ((5 / 12 : ℝ) * k131Prefactor * y ^ (-(27 / 8 : ℝ)) * k131RemainderPoly.eval z) *
        t ^ (-(29 / 16 : ℝ)) := by
  intro z P
  let v := forwardCoord y t
  have hv := forward_coord_pos_le hy ht.le hu
  have hG := forward_eval_mono remainder_poly_coeff hv.1 hv.2
  have hK : 0 ≤ k131Prefactor := by
    unfold k131Prefactor
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact mul_nonneg hA (Real.exp_pos _).le
  have h := k131_trivial_integrand_le hy ht hu
  dsimp only at h
  have he :
    (k131RemainderPoly).eval v =
      ((19 / 16 : ℝ) ^ 2) * gaussianK131Inverse v +
        (2 * (19 / 16 : ℝ)) * gaussianK131InversePoly.derivative.eval v +
        gaussianK131InversePoly.derivative.derivative.eval v := by
    simp only [k131RemainderPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      gaussian_k131_inverse_eval]
  rw [← he] at h
  have hp : 0 < t := zero_lt_one.trans ht
  have h' :
    |deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t| ≤
      (k131Prefactor * y ^ (-(27 / 8 : ℝ)) * t ^ (19 / 16 : ℝ) * k131RemainderPoly.eval v / t) *
        ((5 / 12 : ℝ) * t⁻¹ ^ 2) := by
    rw [← forward_decay_power hy hp,
      mul_assoc ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ)))]
    linarith only [h]
  refine h'.trans ?_
  have hu' :=
    mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hG
          (mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hy.le (-(27 / 8 : ℝ))))
            (Real.rpow_nonneg hp.le (19 / 16 : ℝ))))
        hp.le)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 12) (sq_nonneg t⁻¹))
  refine hu'.trans_eq ?_
  have hpow : t ^ (19 / 16 : ℝ) * t⁻¹ * t⁻¹ ^ 2 = t ^ (-(29 / 16 : ℝ)) := by
    rw [mul_assoc, ← pow_succ', inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hp.le, ←
      Real.rpow_add hp]
    norm_num only [Nat.cast_ofNat]
  rw [← hpow, div_eq_mul_inv]
  ring

private theorem trivial_weight_cont {y a b : ℝ} (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b) :
    ContinuousOn
      (fun t ↦
        deriv (fun u ↦ u * deriv (k131ForwardWeight y) u) t *
          AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t)
      (Set.uIcc a b) := by
  have hs := forward_log_slope_smooth hy
  have hd : ContDiffOn ℝ 0 (deriv (fun u ↦ u * deriv (k131ForwardWeight y) u)) (Set.Ioi 0) :=
    hs.deriv_of_isOpen isOpen_Ioi (by decide)
  refine
    (hd.continuousOn.mono ?_).mul
      (Set.uIcc_of_le hab ▸ AnalyticNumberTheory.RiemannZeta.trivial_cont_closed ha)
  exact fun t ht ↦ zero_lt_one.trans_le (ha.trans (Set.uIcc_of_le hab ▸ ht).1)

private theorem trivial_abs_integral_le {y a b : ℝ} (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ y ^ 2 * Real.exp (9 / 4)) :
    let P := fun u ↦ u * deriv (k131ForwardWeight y) u
    let z := 9 / 4 + 2 * Real.log y
    let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
    (∫ t in a..b, |deriv P t * T t|) ≤
      ((5 / 12 : ℝ) / (2 - 19 / 16)) *
        ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
        y ^ (-(27 / 8 : ℝ)) *
        k131RemainderPoly.eval z := by
  intro P z T
  let K := (5 / 12 : ℝ) * k131Prefactor * y ^ (-(27 / 8 : ℝ)) * k131RemainderPoly.eval z
  let F := fun t ↦ deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t :=
    zero_lt_one.trans_le (ha.trans (Set.uIcc_of_le hab ▸ ht).1)
  have hF : ContinuousOn F (Set.uIcc a b) := trivial_weight_cont hy ha hab
  have hpow : ContinuousOn (fun t : ℝ ↦ t ^ (-(29 / 16 : ℝ))) (Set.uIcc a b) := fun t ht ↦
    (Real.continuousAt_rpow_const t _ (Or.inl (hp t ht).ne')).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mono_on_of_le_Ioo (μ := MeasureTheory.volume) hab
      hF.abs.intervalIntegrable (continuousOn_const.mul (f := fun _ ↦ K) hpow).intervalIntegrable
      (fun t ht ↦ trivial_integrand_power hy (ha.trans_lt ht.1) (ht.2.le.trans hb))
  have he : (∫ t in a..b, t ^ (-(29 / 16 : ℝ))) ≤ 1 / (2 - 19 / 16 : ℝ) := by
    have ha' : 0 < a := zero_lt_one.trans_le ha
    have hn : (0 : ℝ) ∉ Set.uIcc a b := fun h ↦ (lt_irrefl (0 : ℝ)) (hp 0 h)
    rw [integral_rpow (Or.inr ⟨by norm_num only, hn⟩)]
    have hB := Real.rpow_nonneg (ha'.trans_le hab).le (-(29 / 16 : ℝ) + 1)
    have hA : a ^ (-(29 / 16 : ℝ) + 1) ≤ 1 := by
      simpa only [Real.one_rpow] using
        Real.rpow_le_rpow_of_nonpos zero_lt_one ha (by norm_num only : -(29 / 16 : ℝ) + 1 ≤ 0)
    rw [div_le_iff_of_neg (by norm_num only : -(29 / 16 : ℝ) + 1 < 0)]
    have hh : (1 / (2 - 19 / 16 : ℝ)) * (-(29 / 16 : ℝ) + 1) = -1 := by norm_num only
    rw [hh]
    linarith only [hA, hB]
  have hK : 0 ≤ K := by
    have hz :=
      (forward_coord_pos_le hy ha (hab.trans hb)).1.trans
        (forward_coord_pos_le hy ha (hab.trans hb)).2
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only) (mul_nonneg hA (Real.exp_pos _).le))
          (Real.rpow_nonneg hy.le _))
        (forward_eval_nonneg remainder_poly_coeff hz)
  refine hi.trans ?_
  change (∫ t in a..b, K * t ^ (-(29 / 16 : ℝ))) ≤ _
  rw [intervalIntegral.integral_const_mul]
  exact
    (mul_le_mul_of_nonneg_left he hK).trans_eq
      (by
        dsimp only [K, k131Prefactor]; ring)

/-- On any subinterval above 1 in the forward support, the trivial-zero
integral costs at most the principal polynomial times `5/(12(2-d))`. -/
theorem k131_trivial_integral_le {y a b : ℝ} (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ y ^ 2 * Real.exp (9 / 4)) :
    let P := fun u ↦ u * deriv (k131ForwardWeight y) u
    let z := 9 / 4 + 2 * Real.log y
    |∫ t in a..b, deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t| ≤
      ((5 / 12 : ℝ) / (2 - 19 / 16)) *
        ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
        y ^ (-(27 / 8 : ℝ)) *
        k131RemainderPoly.eval z := by
  intro P z
  let F := fun t ↦ deriv P t * AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t
  have h := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := F) hab
  simp only [Real.norm_eq_abs] at h
  exact h.trans (trivial_abs_integral_le hy ha hab hb)

/-- The two trivial-zero integrals and the cutoff contribution share the
single remainder allowance of formula (4.8). -/
theorem k131_trivial_remainder_le {y : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let P := fun t ↦ t * deriv (k131ForwardWeight y) t
    let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
    let F := fun t ↦ deriv P t * T t
    |-3 * (∫ t in (1 : ℝ)..x, F t) + (∫ t in x..u, F t) + 4 * P x * T x| ≤
      3 * ((5 / 12 : ℝ) / (2 - 19 / 16)) *
          ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
          y ^ (-(27 / 8 : ℝ)) *
          k131RemainderPoly.eval z +
        gaussianK131EdgeLoss / y ^ 5 := by
  intro x u z P T F
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hx' : 1 ≤ x := hx.le
  have hpre :=
    intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := F) hx'
  have htail :=
    intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume) (f := F) hxu
  simp only [Real.norm_eq_abs] at hpre htail
  have hi₁ : IntervalIntegrable (fun t ↦ |F t|) MeasureTheory.volume 1 x :=
    (trivial_weight_cont hy le_rfl hx').abs.intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t ↦ |F t|) MeasureTheory.volume x u :=
    (trivial_weight_cont hy hx' hxu).abs.intervalIntegrable
  have hs := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  have ht : 0 ≤ ∫ t in x..u, |F t| :=
    intervalIntegral.integral_nonneg hxu (fun t _ ↦ abs_nonneg (F t))
  have hI := trivial_abs_integral_le hy (a := 1) (b := u) le_rfl (hx'.trans hxu) le_rfl
  have he := k131_trivial_edge_le hy hx
  have htri :=
    (abs_add_le (-3 * (∫ t in (1 : ℝ)..x, F t) + (∫ t in x..u, F t)) (4 * P x * T x)).trans
      (add_le_add_left (abs_add_le (-3 * ∫ t in (1 : ℝ)..x, F t) (∫ t in x..u, F t)) _)
  rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)] at htri
  refine htri.trans ?_
  change |4 * P x * T x| ≤ _ at he
  change (∫ t in (1 : ℝ)..u, |F t|) ≤ _ at hI
  linarith only [hpre, htail, hs, ht, hI, he]

private theorem principal_linear_parts {y a b c : ℝ} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) :
    let f := k131ForwardWeight y
    let P := fun t ↦ t * deriv f t
    let A := fun t ↦ t - c * Real.log t
    (∫ t in a..b, deriv P t * A t) =
      P b * A b - P a * A a - ((b - c) * f b - (a - c) * f a - ∫ t in a..b, f t) := by
  intro f P A
  have hpos (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := ha.trans_le (Set.uIcc_of_le hab ▸ ht).1
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hd0 : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
  have hD : ContinuousOn (deriv P) (Set.uIcc a b) := hd0.continuousOn.mono hpos
  have hP (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt P (deriv P t) t :=
    (((hs.differentiableOn (by decide)) t (hpos t ht)).differentiableAt
        (isOpen_Ioi.mem_nhds (hpos t ht))).hasDerivAt
  have hA (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt A (1 - c * t⁻¹) t :=
    (hasDerivAt_id t).sub ((Real.hasDerivAt_log (hpos t ht).ne').const_mul c)
  have hi : IntervalIntegrable (fun t : ℝ ↦ 1 - c * t⁻¹) MeasureTheory.volume a b :=
    (continuousOn_const.sub
        (continuousOn_const.mul
          (continuousOn_id.inv₀ (fun t ht ↦ (hpos t ht).ne')))).intervalIntegrable
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hA hP hi hD.intervalIntegrable
  have hf (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt f (deriv f t) t :=
    (forward_weight_deriv hy (hpos t ht)).differentiableAt.hasDerivAt
  have hdf : ContinuousOn (deriv f) (Set.uIcc a b) := fun t ht ↦
    (forward_slope_continuous hy (hpos t ht)).continuousWithinAt
  have hf' :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun t _ ↦ (hasDerivAt_id t).sub_const c) hf
      (continuous_const.intervalIntegrable a b) hdf.intervalIntegrable
  have he : (∫ t in a..b, (1 - c * t⁻¹) * P t) = ∫ t in a..b, (t - c) * deriv f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change (1 - c * t⁻¹) * (t * deriv f t) = (t - c) * deriv f t
    field_simp [(hpos t ht).ne']
  rw [he] at h
  simp only [id_eq, one_mul] at hf'
  rw [hf'] at h
  simpa only [mul_comm (A _) (deriv P _), mul_comm (A _) (P _)] using h

/-- Separate the main mass, the logarithmic term and the centered error
from the twice-transformed principal sum. The lower endpoint is 1,
so the formula retains the two corresponding lower-end corrections. -/
theorem k131_principal_centered {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) (c : ℝ) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let w := fun n : ℕ ↦ f n * ArithmeticFunction.vonMangoldt n
    let P := fun t ↦ t * deriv f t
    let E := fun t ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t + c * Real.log t
    4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) =
      3 * (∫ t in (1 : ℝ)..x, f t) - (∫ t in x..u, f t) +
            4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x + c) +
            3 * (1 - c) * f 1 -
          3 * P 1 +
        (3 * (∫ t in (1 : ℝ)..x, deriv P t * E t) - (∫ t in x..u, deriv P t * E t) -
          4 * P x * E x) := by
  intro x u f w P E
  let A := fun t : ℝ ↦ t - c * Real.log t
  let M := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hd0 : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
  have hsplit {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, deriv P t * M t) =
      (∫ t in a..b, deriv P t * E t) + ∫ t in a..b, deriv P t * A t := by
    have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t :=
      zero_lt_one.trans_le (ha.trans (Set.uIcc_of_le hab ▸ ht).1)
    have hM : ContinuousOn M (Set.uIcc a b) := by
      have hm :=
        AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled
          (show (0 : ℝ) < 1 from zero_lt_one) b
      simp only [one_mul] at hm
      exact hm.mono (fun t ht ↦ ⟨(hp t ht).le, (Set.uIcc_of_le hab ▸ ht).2⟩)
    have hl : ContinuousOn Real.log (Set.uIcc a b) := fun t ht ↦
      (Real.continuousAt_log (hp t ht).ne').continuousWithinAt
    have hc : ContinuousOn (fun t ↦ c * Real.log t) (Set.uIcc a b) := continuousOn_const.mul hl
    have hA : ContinuousOn A (Set.uIcc a b) := continuousOn_id.sub hc
    have hE : ContinuousOn E (Set.uIcc a b) := (hM.sub continuousOn_id).add hc
    have hD : ContinuousOn (deriv P) (Set.uIcc a b) := hd0.continuousOn.mono hp
    have hIE : IntervalIntegrable (fun t ↦ deriv P t * E t) MeasureTheory.volume a b :=
      (hD.mul hE).intervalIntegrable
    have hIA : IntervalIntegrable (fun t ↦ deriv P t * A t) MeasureTheory.volume a b :=
      (hD.mul hA).intervalIntegrable
    rw [← intervalIntegral.integral_add hIE hIA]
    apply intervalIntegral.integral_congr
    intro t _
    change deriv P t * M t = deriv P t * E t + deriv P t * A t
    dsimp only [E, A, M]
    ring
  rw [k131_principal_second_abel hy hx]
  change
    4 * (gaussianK131UnitWeight / y) * Chebyshev.psi x - 4 * P x * M x +
          3 * (∫ t in (1 : ℝ)..x, deriv P t * M t) -
        (∫ t in x..u, deriv P t * M t) =
      _
  have hlin {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, deriv P t * A t) =
      P b * A b - P a * A a - ((b - c) * f b - (a - c) * f a - ∫ t in a..b, f t) :=
    principal_linear_parts hy ha hab
  have hx' : 1 ≤ x := hx
  rw [hsplit le_rfl hx', hsplit hx' hxu, hlin zero_lt_one hx',
    hlin (show 0 < x from pow_pos hy 2) hxu]
  have hP : P u = 0 := by
    change u * deriv (k131ForwardWeight y) (y ^ 2 * Real.exp (9 / 4)) = 0
    rw [forward_slope_right hy, mul_zero]
  have hf : f u = 0 := forward_weight_right hy
  have hf' : f x = gaussianK131UnitWeight / y := forward_weight_left hy
  rw [hP, hf, hf']
  dsimp only [E, M, A]
  rw [Real.log_one]
  ring

private theorem principal_error_split {y a b : ℝ} (hy : 0 < y) (ha : 1 ≤ a) (hab : a ≤ b) :
    let P := fun t ↦ t * deriv (k131ForwardWeight y) t
    let E := fun t ↦
      AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
        Real.log (2 * Real.pi) * Real.log t
    let Z := fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
    let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
    let C := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
    (∫ t in a..b, deriv P t * E t) =
      (∫ t in a..b, deriv P t * Z t) - (∫ t in a..b, deriv P t * T t) - C * (P b - P a) := by
  intro P E Z T C
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hd0 : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ∈ Set.Ioi (0 : ℝ) :=
    zero_lt_one.trans_le (ha.trans (Set.uIcc_of_le hab ▸ ht).1)
  have hd := hd0.continuousOn.mono hp
  have hz : ContinuousOn Z (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    exact
      Complex.continuous_re.continuousOn.comp
        (AnalyticNumberTheory.RiemannZeta.zero_sum_continuous ha) (fun _ _ ↦ Set.mem_univ _)
  have ht : ContinuousOn T (Set.uIcc a b) :=
    Set.uIcc_of_le hab ▸ AnalyticNumberTheory.RiemannZeta.trivial_cont_closed ha
  have hZ : IntervalIntegrable (fun t ↦ deriv P t * Z t) MeasureTheory.volume a b :=
    (hd.mul hz).intervalIntegrable
  have hT : IntervalIntegrable (fun t ↦ deriv P t * T t) MeasureTheory.volume a b :=
    (hd.mul ht).intervalIntegrable
  have hC := hd.intervalIntegrable (μ := MeasureTheory.volume)
  have hft :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        (((hs.differentiableOn (by decide)) t (hp t ht)).differentiableAt
            (isOpen_Ioi.mem_nhds (hp t ht))).hasDerivAt)
      hC
  rw [← hft, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hZ hT, ←
    intervalIntegral.integral_sub (hZ.sub hT) (hC.const_mul C)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with t ht'
  have ht1 : 1 < t := ha.trans_lt (Set.uIoc_of_le hab ▸ ht').1
  have he := k131_centered_trivial_part ht1
  change E t + C - Z t = -T t at he
  change deriv P t * E t = deriv P t * Z t - deriv P t * T t - C * deriv P t
  linear_combination deriv P t * he

/-- The nontrivial-zero term of the principal sum with lower endpoint 1. -/
noncomputable def k131PrincipalSpectral (y : ℝ) : ℝ :=
  let x := y ^ 2
  let u := x * Real.exp (9 / 4)
  let P := fun t ↦ t * deriv (k131ForwardWeight y) t
  let Z := fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re
  3 * (∫ t in (1 : ℝ)..x, deriv P t * Z t) - (∫ t in x..u, deriv P t * Z t) - 4 * P x * Z x

private theorem principal_zero_integral_limit {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {Q : ℝ → ℝ}
    (hQ : ContinuousOn Q (Set.Icc a b)) :
    let S := fun m ↦
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
            (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
            (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
        (fun ρ ↦ ¬ρ.re < 0)
    let Z := AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution
    Filter.Tendsto (fun m ↦ ∑ ρ ∈ S m, ∫ t in a..b, Q t * (Z t ρ).re) Filter.atTop
      (nhds
        (∫ t in a..b,
          Q t * (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)) := by
  intro S Z
  have h := AnalyticNumberTheory.RiemannZeta.weighted_zero_integral_limit ha hab hQ
  simp only [mul_comm] at h
  refine h.congr' ?_
  filter_upwards with m
  have he (t : ℝ) : (∑ ρ ∈ S m, Z t ρ).re * Q t = ∑ ρ ∈ S m, (Z t ρ).re * Q t := by
    rw [Complex.re_sum, Finset.sum_mul]
  change (∫ t in a..b, Q t * (∑ ρ ∈ S m, Z t ρ).re) = _
  simp only [mul_comm (Q _), he]
  rw [intervalIntegral.integral_finsetSum]
  intro ρ hρ
  have hs := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hs.1).2
  have hterm : (Z · ρ) = fun t ↦ AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ := by
    funext t
    simp only [Z, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm, hz, true_and,
      not_lt.mp hs.2, ite_true]
  have hc : ContinuousOn (fun t ↦ (Z t ρ).re) (Set.Icc a b) := by
    change ContinuousOn (Complex.re ∘ (Z · ρ)) (Set.Icc a b)
    rw [hterm]
    exact
      Complex.continuous_re.comp_continuousOn
        (AnalyticNumberTheory.RiemannZeta.zero_term_continuous (zero_lt_one.trans_le ha) ρ)
  exact (hc.mul hQ).intervalIntegrable_of_Icc hab

/-- The K131 spectral correction is the limit of the sum of its individual
zero contributions over the same rectangles as the explicit formula. -/
theorem k131_principal_spectral_limit {y : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let P := fun t ↦ t * deriv (k131ForwardWeight y) t
    let S := fun m ↦
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
            (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
            (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
        (fun ρ ↦ ¬ρ.re < 0)
    let Z := AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution
    Filter.Tendsto
      (fun m ↦
        ∑ ρ ∈ S m,
          (3 * (∫ t in (1 : ℝ)..x, deriv P t * (Z t ρ).re) - (∫ t in x..u, deriv P t * (Z t ρ).re) -
            4 * P x * (Z x ρ).re))
      Filter.atTop (nhds (k131PrincipalSpectral y)) := by
  intro x u P S Z
  have hx' : 1 ≤ x := hx.le
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hd : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
  have hc {a b : ℝ} (ha : 1 ≤ a) : ContinuousOn (deriv P) (Set.Icc a b) :=
    hd.continuousOn.mono (fun _ ht ↦ zero_lt_one.trans_le (ha.trans ht.1))
  have h₁ := principal_zero_integral_limit le_rfl hx' (hc le_rfl)
  have h₂ := principal_zero_integral_limit hx' hxu (hc hx')
  have h₃ :=
    (Complex.continuous_re.tendsto _).comp (AnalyticNumberTheory.RiemannZeta.log_zero_tsum_limit hx)
  have h := (((h₁.const_mul 3).sub h₂).sub (h₃.const_mul (4 * P x)))
  refine h.congr' ?_
  filter_upwards with m
  change
    3 * (∑ ρ ∈ S m, ∫ t in (1 : ℝ)..x, deriv P t * (Z t ρ).re) -
        (∑ ρ ∈ S m, ∫ t in x..u, deriv P t * (Z t ρ).re) -
        4 * P x * (∑ ρ ∈ S m, Z x ρ).re =
      _
  rw [Complex.re_sum]
  simp only [Finset.mul_sum, Finset.sum_sub_distrib]

private theorem real_cpow_coeff_deriv {t : ℝ} (ht : 0 < t) {ρ : ℂ} (hρ : ρ ≠ 0) (c : ℂ) :
    HasDerivAt (fun v : ℝ ↦ (c * (v : ℂ) ^ ρ).re) ((c * ρ * (t : ℂ) ^ ρ).re / t) t := by
  have hc := (hasDerivAt_ofReal_cpow_const ht.ne' hρ).const_mul c
  have hd := (hasDerivAt_const t Complex.reCLM).clm_apply hc
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have h : c * (ρ * (t : ℂ) ^ (ρ - 1)) = (c * ρ * (t : ℂ) ^ ρ) / (t : ℂ) := by
    rw [Complex.cpow_sub _ _ htC, Complex.cpow_one]
    ring
  simpa only [zero_apply, zero_add, Complex.reCLM_apply, h, Complex.div_ofReal_re] using hd

private theorem zero_log_parts {y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) {ρ : ℂ}
    (hρ : ρ ≠ 0) (c : ℂ) :
    let f := k131ForwardWeight y
    let P := fun t ↦ t * deriv f t
    let Z := fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re
    let W := fun t : ℝ ↦ (c * ρ * (t : ℂ) ^ ρ).re
    let V := fun t : ℝ ↦ (c * ρ * ρ * (t : ℂ) ^ ρ).re
    (∫ t in a..b, deriv P t * Z t) =
      P b * Z b - P a * Z a - (f b * W b - f a * W a) + ∫ t in a..b, f t * (V t / t) := by
  intro f P Z W V
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : t ∈ Set.Ioi (0 : ℝ) :=
    ha.trans_le (Set.uIcc_of_le hab ▸ ht).1
  have hs : ContDiffOn ℝ 1 P (Set.Ioi 0) := forward_log_slope_smooth hy
  have hd0 : ContDiffOn ℝ 0 (deriv P) (Set.Ioi 0) := hs.deriv_of_isOpen isOpen_Ioi (by decide)
  have hP (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt P (deriv P t) t :=
    (((hs.differentiableOn (by decide)) t (hp t ht)).differentiableAt
        (isOpen_Ioi.mem_nhds (hp t ht))).hasDerivAt
  have hf (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt f (deriv f t) t :=
    (forward_weight_deriv hy (hp t ht)).differentiableAt.hasDerivAt
  have hZ (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt Z (W t / t) t :=
    real_cpow_coeff_deriv (hp t ht) hρ c
  have hW (t : ℝ) (ht : t ∈ Set.uIcc a b) : HasDerivAt W (V t / t) t :=
    real_cpow_coeff_deriv (hp t ht) hρ (c * ρ)
  have hdiv (c' : ℂ) : ContinuousOn (fun t : ℝ ↦ (c' * (t : ℂ) ^ ρ).re / t) (Set.uIcc a b) :=
    fun t ht ↦
    (((real_cpow_coeff_deriv (hp t ht) hρ c').continuousAt).div continuousAt_id
        (show t ≠ 0 from (hp t ht).ne')).continuousWithinAt
  have h₁ :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hZ hP (hdiv (c * ρ)).intervalIntegrable
      (hd0.continuousOn.mono hp).intervalIntegrable
  have h₂ :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul hW hf (hdiv (c * ρ * ρ)).intervalIntegrable
      (show ContinuousOn (deriv f) (Set.uIcc a b) from fun t ht ↦
          (forward_slope_continuous hy (hp t ht)).continuousWithinAt).intervalIntegrable
  have he : (∫ t in a..b, W t / t * P t) = ∫ t in a..b, W t * deriv f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change W t / t * (t * deriv f t) = W t * deriv f t
    rw [← mul_assoc, div_mul_cancel₀ _ (show t ≠ 0 from (hp t ht).ne')]
  rw [he, h₂] at h₁
  simpa only [mul_comm (Z _) (deriv P _), mul_comm (Z _) (P _), mul_comm (W _) (f _),
    mul_comm (V _ / _) (f _), sub_sub_eq_add_sub, sub_eq_add_neg, neg_add, neg_neg, add_assoc,
    add_comm, add_left_comm] using h₁

/-- For an individual zero term, two integrations by parts cancel the
logarithmic-slope boundary at the cutoff and leave the forward Mellin integrals. -/
theorem k131_zero_boundary_cancel {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) {ρ : ℂ} (hρ : ρ ≠ 0)
    (c : ℂ) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let P := fun t ↦ t * deriv f t
    let Z := fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re
    let W := fun t : ℝ ↦ (c * ρ * (t : ℂ) ^ ρ).re
    let I := fun t : ℝ ↦ f t * ((c * ρ * ρ * (t : ℂ) ^ ρ).re / t)
    3 * (∫ t in (1 : ℝ)..x, deriv P t * Z t) - (∫ t in x..u, deriv P t * Z t) - 4 * P x * Z x =
      -4 * (gaussianK131UnitWeight / y) * W x + 3 * (∫ t in (1 : ℝ)..x, I t) - (∫ t in x..u, I t) +
        3 * (f 1 * W 1 - P 1 * Z 1) := by
  intro x u f P Z W I
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hx' : 1 ≤ x := hx
  have hx0 : 0 < x := pow_pos hy 2
  have hab {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, deriv P t * Z t) =
      P b * Z b - P a * Z a - (f b * W b - f a * W a) + ∫ t in a..b, I t :=
    zero_log_parts hy ha hab hρ c
  rw [hab zero_lt_one hx', hab hx0 hxu]
  have hP : P u = 0 := by
    change u * deriv (k131ForwardWeight y) (y ^ 2 * Real.exp (9 / 4)) = 0
    rw [forward_slope_right hy, mul_zero]
  have hu : f u = 0 := forward_weight_right hy
  have hf : f x = gaussianK131UnitWeight / y := forward_weight_left hy
  rw [hP, hu, hf]
  ring

private theorem forward_cpow_coord {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (ρ : ℂ) :
    (t : ℂ) ^ ρ =
      Complex.exp (((9 / 4 + 2 * Real.log y : ℝ) : ℂ) * ρ) *
        Complex.exp (-(forwardCoord y t : ℂ) * ρ) := by
  have hlog : Real.log t = 9 / 4 + 2 * Real.log y - forwardCoord y t := by
    unfold forwardCoord
    rw [Real.log_div ht.ne' (pow_pos hy 2).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), ← Complex.ofReal_log ht.le, ←
    Complex.exp_add]
  congr 1
  rw [hlog, Complex.ofReal_sub]
  ring

private theorem forward_mellin_coord_at {y t : ℝ} (hy : 0 < y) (ht : 0 < t) (c ρ : ℂ) :
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let C := c * Complex.exp (((9 / 4 + 2 * Real.log y : ℝ) : ℂ) * ρ)
    let v := forwardCoord y t
    k131ForwardWeight y t * ((c * (t : ℂ) ^ ρ).re / t) =
      K *
        (((C * Complex.exp (-((19 / 16 : ℂ) + ρ) * (v : ℂ))).re * gaussianK131Inverse v) *
          t⁻¹) := by
  intro K C v
  rw [forward_weight_profile hy ht, forward_cpow_coord hy ht]
  have he :
    Complex.exp (-((19 / 16 : ℂ) + ρ) * (v : ℂ)) =
      (Real.exp (-(19 / 16 : ℝ) * v) : ℂ) * Complex.exp (-(v : ℂ) * ρ) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, Complex.ofReal_mul, Complex.ofReal_neg]
    push_cast
    congr 1
    ring
  rw [he]
  unfold recoveryProfile
  dsimp only [C]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im]
  ring

/-- Write a forward zero Mellin integral as an exponential polynomial in
the reversed logarithmic coordinate, retaining the complex phase. -/
theorem k131_forward_mellin_coord {y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) (c ρ : ℂ) :
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let C := c * Complex.exp (((9 / 4 + 2 * Real.log y : ℝ) : ℂ) * ρ)
    (∫ t in a..b, k131ForwardWeight y t * ((c * (t : ℂ) ^ ρ).re / t)) =
      K *
        ∫ v in forwardCoord y b..forwardCoord y a,
          (C * Complex.exp (-((19 / 16 : ℂ) + ρ) * (v : ℂ))).re * gaussianK131Inverse v := by
  intro K C
  let g := fun v : ℝ ↦ (C * Complex.exp (-((19 / 16 : ℂ) + ρ) * (v : ℂ))).re * gaussianK131Inverse v
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := ha.trans_le (Set.uIcc_of_le hab ▸ ht).1
  have hd : ContinuousOn (fun t : ℝ ↦ -t⁻¹) (Set.uIcc a b) :=
    (continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')).neg
  have hB : Continuous gaussianK131Inverse := by
    rw [←
      show gaussianK131InversePoly.eval = gaussianK131Inverse from
        funext gaussian_k131_inverse_eval]
    exact gaussianK131InversePoly.continuous
  have hg : Continuous g :=
    (Complex.continuous_re.comp
          (continuous_const.mul
            (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))).mul
      hB
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (a := a) (b := b) (f := forwardCoord y) (f' := fun t ↦
      -t⁻¹) (g := g) (fun t ht ↦ forward_coord_deriv hy (hp t ht)) hd hg.continuousOn
  rw [intervalIntegral.integral_symm (f := g) (forwardCoord y b) (forwardCoord y a)] at h
  simp only [Function.comp_def, mul_neg, intervalIntegral.integral_neg, neg_inj] at h
  rw [← h, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  exact forward_mellin_coord_at hy (hp t ht) c ρ

/-- The two Mellin integrals in the individual spectral contribution use
the same complex exponential polynomial, split at the fixed coordinate 9/4. -/
theorem k131_zero_contribution_coord {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) {ρ : ℂ} (hρ : ρ ≠ 0)
    (c : ℂ) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let P := fun t ↦ t * deriv f t
    let Z := fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re
    let W := fun t : ℝ ↦ (c * ρ * (t : ℂ) ^ ρ).re
    let z := 9 / 4 + 2 * Real.log y
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let C := c * ρ * ρ * Complex.exp ((z : ℂ) * ρ)
    let g := fun v : ℝ ↦
      (C * Complex.exp (-((19 / 16 : ℂ) + ρ) * (v : ℂ))).re * gaussianK131Inverse v
    3 * (∫ t in (1 : ℝ)..x, deriv P t * Z t) - (∫ t in x..u, deriv P t * Z t) - 4 * P x * Z x =
      -4 * (gaussianK131UnitWeight / y) * W x +
        K * (3 * (∫ v in (9 / 4 : ℝ)..z, g v) - ∫ v in (0 : ℝ)..9 / 4, g v) +
        3 * (f 1 * W 1 - P 1 * Z 1) := by
  intro x u f P Z W z K C g
  have hx' : 1 ≤ x := hx
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have hpos : 0 < x := pow_pos hy 2
  have hc : forwardCoord y x = 9 / 4 := by
    unfold forwardCoord
    rw [show x = y ^ 2 from rfl, div_self hpos.ne', Real.log_one, sub_zero]
  have hu : forwardCoord y u = 0 := by
    unfold forwardCoord u
    rw [show y ^ 2 = x from rfl, mul_div_cancel_left₀ _ hpos.ne', Real.log_exp, sub_self]
  have hz : forwardCoord y 1 = z := by
    unfold forwardCoord z
    rw [one_div, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [k131_zero_boundary_cancel hy hx hρ c,
    k131_forward_mellin_coord hy zero_lt_one hx' (c * ρ * ρ) ρ,
    k131_forward_mellin_coord hy hpos hxu (c * ρ * ρ) ρ, hc, hu, hz]
  dsimp only [x, z, K, g, C]
  ring

/-- The signed combination of the zero Mellin integrals uses three
evaluations of the complex antiderivative, at 0, 9/4 and the lower cutoff. -/
theorem k131_zero_mellin_endpoints {s : ℂ} (hs : s ≠ 0) (c : ℂ) (z : ℝ) :
    let g := fun v : ℝ ↦ (c * Complex.exp (-s * (v : ℂ))).re * gaussianK131Inverse v
    let Q := k131AntiPoly (gaussianK131InversePoly.map Complex.ofRealHom) s
    let F := fun v : ℝ ↦ (c * Complex.exp (-s * (v : ℂ)) * Q.eval (v : ℂ)).re
    3 * (∫ v in (9 / 4 : ℝ)..z, g v) - (∫ v in (0 : ℝ)..9 / 4, g v) =
      4 * F (9 / 4) - F 0 - 3 * F z := by
  intro g Q F
  let P := gaussianK131InversePoly.map Complex.ofRealHom
  have hP : P.natDegree < 20 := Polynomial.natDegree_map_le.trans_lt forward_inverse_degree
  have hEval (v : ℝ) : P.eval (v : ℂ) = (gaussianK131Inverse v : ℂ) := by
    unfold P
    rw [Polynomial.eval_map]
    change gaussianK131InversePoly.eval₂ Complex.ofRealHom (Complex.ofRealHom v) = _
    rw [Polynomial.eval₂_hom, gaussian_k131_inverse_eval]
    rfl
  have he (a b : ℝ) : (∫ v in a..b, g v) = F a - F b := by
    have hi := k131_complex_exp_integral hP hs c a b
    have hr (w : ℂ) (r : ℝ) : (w * (r : ℂ)).re = w.re * r := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    simp only [hEval, hr, Complex.sub_re] at hi
    exact hi
  rw [he, he]
  ring

/-- The individual spectral contribution in closed endpoint form. The
terms at the lower integration endpoint retain the cutoff correction. -/
noncomputable def k131ZeroEndpoint (y : ℝ) (ρ c : ℂ) : ℝ :=
  let x := y ^ 2
  let z := 9 / 4 + 2 * Real.log y
  let f := k131ForwardWeight y
  let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
  let s := (19 / 16 : ℂ) + ρ
  let Q := k131AntiPoly (gaussianK131InversePoly.map Complex.ofRealHom) s
  let C := c * ρ * ρ * Complex.exp ((z : ℂ) * ρ)
  let F := fun v : ℝ ↦ (C * Complex.exp (-s * (v : ℂ)) * Q.eval (v : ℂ)).re
  (-4) * (gaussianK131UnitWeight / y) * (c * ρ * (x : ℂ) ^ ρ).re +
    K * (4 * F (9 / 4) - F 0 - 3 * F z) +
    3 * (f 1 * (c * ρ).re - deriv f 1 * c.re)

/-- Evaluate the individual spectral contribution using only complex
polynomial values and endpoint factors. -/
theorem k131_zero_endpoint_eq {y : ℝ} (hy : 0 < y) (hx : 1 ≤ y ^ 2) {ρ : ℂ} (hρ : ρ ≠ 0)
    (hs : (19 / 16 : ℂ) + ρ ≠ 0) (c : ℂ) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let P := fun t ↦ t * deriv (k131ForwardWeight y) t
    let Z := fun t : ℝ ↦ (c * (t : ℂ) ^ ρ).re
    3 * (∫ t in (1 : ℝ)..x, deriv P t * Z t) - (∫ t in x..u, deriv P t * Z t) - 4 * P x * Z x =
      k131ZeroEndpoint y ρ c := by
  intro x u P Z
  rw [k131_zero_contribution_coord hy hx hρ c, k131_zero_mellin_endpoints hs]
  simp only [k131ZeroEndpoint, mul_one, one_mul, Complex.ofReal_one, Complex.one_cpow]

/-- The nonnegative-real-part zeros inside the explicit-formula rectangle. -/
noncomputable def k131ZeroRect (m : ℕ) : Finset ℂ :=
  (AnalyticNumberTheory.RiemannZeta.riemannZetaZerosInAnyRectangle
        (AnalyticNumberTheory.RiemannZeta.unifiedRectangleLower m)
        (AnalyticNumberTheory.RiemannZeta.unifiedTauRectangleUpper 2 m)).filter
    (fun ρ ↦ ¬ρ.re < 0)

/-- The endpoint contribution with the signed coefficient of the zeta
logarithmic explicit formula, including the multiplicity of the zero. -/
noncomputable def k131ZetaEndpoint (y : ℝ) (ρ : ℂ) : ℝ :=
  k131ZeroEndpoint y ρ
    (-(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2)

/-- Summing the evaluated endpoint contributions over the explicit-formula
rectangles converges to the principal nontrivial-zero correction. -/
theorem k131_zeta_endpoint_limit {y : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2) :
    Filter.Tendsto (fun m ↦ ∑ ρ ∈ k131ZeroRect m, k131ZetaEndpoint y ρ) Filter.atTop
      (nhds (k131PrincipalSpectral y)) := by
  have h := k131_principal_spectral_limit hy hx
  dsimp only at h
  refine h.congr' ?_
  filter_upwards with m
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hr := Finset.mem_filter.mp hρ
  have hz := (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp hr.1).2
  have hne : ρ ≠ 0 := by
    intro he
    rw [he, riemannZeta_zero] at hz
    norm_num only at hz
  have hs : (19 / 16 : ℂ) + ρ ≠ 0 := by
    intro he
    rw [show (19 / 16 : ℂ) = ((19 / 16 : ℝ) : ℂ) by
        push_cast; rfl] at he
    have hh := congrArg Complex.re he
    simp only [Complex.add_re, Complex.zero_re, Complex.ofReal_re] at hh
    linarith only [hh, not_lt.mp hr.2]
  unfold AnalyticNumberTheory.RiemannZeta.riemannZetaLogZeroContribution
  have he :=
    k131_zero_endpoint_eq hy hx.le hne hs
      (-(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2)
  simpa only [div_mul_eq_mul_div, k131ZetaEndpoint] using he

/-- Bound an endpoint polynomial by the sum of the norms of its derivatives
divided by successive powers of any positive lower bound for the rate norm. -/
theorem k131_anti_norm_le {P : Polynomial ℂ} {s v : ℂ} {h : ℝ} (hh : 0 < h) (hs : h ≤ ‖s‖) :
    ‖(k131AntiPoly P s).eval v‖ ≤
      ∑ j ∈ Finset.range 20, ‖((Polynomial.derivative^[j]) P).eval v‖ / h ^ (j + 1) := by
  simp only [k131AntiPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  rw [norm_mul, norm_inv, norm_pow, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hh _) (pow_le_pow_left₀ hh.le hs _)

private theorem anti_difference_eval {F : Type*} [Field F] (P : Polynomial F) (d s v : F) :
    (k131AntiPoly (Polynomial.C d * P - P.derivative) s).eval v =
      d * (k131AntiPoly P s).eval v - (k131AntiPoly P s).derivative.eval v := by
  have hs (j : ℕ) :
    (Polynomial.derivative^[j]) P.derivative = ((Polynomial.derivative^[j]) P).derivative := by
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  simp only [k131AntiPoly, Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_C_mul,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.derivative_sum, Polynomial.derivative_C_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [hs]
  ring

/-- At the cutoff, the order-one terms cancel. The remaining quotient has
the antiderivative of the slope polynomial and a separate inverse zero factor. -/
theorem k131_cutoff_cancel {P : Polynomial ℂ} (hP : P.natDegree < 20) {ρ d v : ℂ} (hρ : ρ ≠ 0)
    (hs : d + ρ ≠ 0) :
    P.eval v / ρ - (k131AntiPoly P (d + ρ)).eval v =
      (k131AntiPoly (Polynomial.C d * P - P.derivative) (d + ρ)).eval v / ρ := by
  rw [anti_difference_eval]
  have h := moment_poly_deriv hP hs v
  field_simp [hρ]
  linear_combination h

/-- The physical lower endpoint combines three terms into the second
logarithmic derivative polynomial divided by the square of the zero. -/
theorem k131_lower_cancel {P : Polynomial ℂ} (hP : P.natDegree < 20) {ρ d v : ℂ} (hρ : ρ ≠ 0)
    (hs : d + ρ ≠ 0) :
    let D := Polynomial.C d * P - P.derivative
    (k131AntiPoly P (d + ρ)).eval v - P.eval v / ρ + D.eval v / ρ ^ 2 =
      (k131AntiPoly (Polynomial.C d * D - D.derivative) (d + ρ)).eval v / ρ ^ 2 := by
  intro D
  have hD : D.natDegree < 20 := by
    exact
      ((Polynomial.natDegree_sub_le _ _).trans
            (max_le (Polynomial.natDegree_C_mul_le _ _)
              ((Polynomial.natDegree_derivative_le P).trans (Nat.sub_le _ _)))).trans_lt
        hP
  have h₁ := k131_cutoff_cancel hP (v := v) hρ hs
  have h₂ := k131_cutoff_cancel hD (v := v) hρ hs
  change P.eval v / ρ - (k131AntiPoly P (d + ρ)).eval v = (k131AntiPoly D (d + ρ)).eval v / ρ at h₁
  calc
    _ = (D.eval v / ρ - (k131AntiPoly D (d + ρ)).eval v) / ρ := by
      rw [sub_div, ← h₁, div_div, pow_two]
      ring
    _ = _ := by rw [h₂, div_div, pow_two]

/-- The cutoff contribution is bounded by inverse powers starting at
order two, using the same lower height for both rate norms. -/
theorem k131_cutoff_norm_le {P : Polynomial ℂ} (hP : P.natDegree < 20) {ρ d v : ℂ} {h : ℝ}
    (hh : 0 < h) (hρ : h ≤ ‖ρ‖) (hs : h ≤ ‖d + ρ‖) :
    ‖P.eval v / ρ - (k131AntiPoly P (d + ρ)).eval v‖ ≤
      ∑ j ∈ Finset.range 20,
        ‖((Polynomial.derivative^[j]) (Polynomial.C d * P - P.derivative)).eval v‖ /
          h ^ (j + 2) := by
  rw [k131_cutoff_cancel hP (norm_pos_iff.mp (hh.trans_le hρ)) (norm_pos_iff.mp (hh.trans_le hs)),
    norm_div]
  refine (div_le_div_of_nonneg_right (k131_anti_norm_le hh hs) (norm_nonneg _)).trans ?_
  refine
    (div_le_div_of_nonneg_left
          (Finset.sum_nonneg fun _ _ ↦ div_nonneg (norm_nonneg _) (pow_nonneg hh.le _)) hh
          hρ).trans_eq
      ?_
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [div_div, ← pow_succ]

/-- At the K131 split, a positive lower bound for the ordinate controls the
cancelled Mellin coefficient through the derivatives of the fixed slope polynomial. -/
theorem k131_split_norm_le {ρ : ℂ} {h : ℝ} (hh : 0 < h) (hρ : h ≤ |ρ.im|) :
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let d : ℂ := 19 / 16
    let b : ℂ := 9 / 4
    ‖B.eval b / ρ - (k131AntiPoly B (d + ρ)).eval b‖ ≤
      ∑ j ∈ Finset.range 20,
        ‖((Polynomial.derivative^[j]) (Polynomial.C d * B - B.derivative)).eval b‖ /
          h ^ (j + 2) := by
  intro B d b
  have hB : B.natDegree < 20 := Polynomial.natDegree_map_le.trans_lt forward_inverse_degree
  have hd : (d + ρ).im = ρ.im := by
    have hd' : d = ((19 / 16 : ℝ) : ℂ) := by
      unfold d; push_cast; rfl
    rw [hd', Complex.add_im, Complex.ofReal_im, zero_add]
  exact
    k131_cutoff_norm_le hB hh (hρ.trans (Complex.abs_im_le_norm ρ))
      (hρ.trans
        (by
          rw [← hd]; exact Complex.abs_im_le_norm _))

/-- In the actual zeta endpoint term, the two contributions at the
cutoff share the same phase and give the cancelled coefficient. -/
theorem k131_zeta_split_eq {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hρ : ρ ≠ 0) :
    let x := y ^ 2
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let c := -m / ρ ^ 2
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let s := (19 / 16 : ℂ) + ρ
    let Q := k131AntiPoly B s
    let F := fun v : ℝ ↦
      (c * ρ * ρ * Complex.exp ((z : ℂ) * ρ) * Complex.exp (-s * (v : ℂ)) * Q.eval (v : ℂ)).re
    k131ZetaEndpoint y ρ =
      (4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) / y) *
            (m * (x : ℂ) ^ ρ * (B.eval (9 / 4) / ρ - Q.eval (9 / 4))).re -
          K * (F 0 + 3 * F z) +
        3 * (f 1 * (c * ρ).re - deriv f 1 * c.re) := by
  intro x z f m c K B s Q F
  let b : ℝ := 9 / 4
  have hB : B.eval (b : ℂ) = (gaussianK131Inverse b : ℂ) := by
    unfold B
    rw [Polynomial.eval_map]
    change gaussianK131InversePoly.eval₂ Complex.ofRealHom (Complex.ofRealHom b) = _
    rw [Polynomial.eval₂_hom, gaussian_k131_inverse_eval]
    rfl
  have hz :
    Complex.exp ((z : ℂ) * ρ) * Complex.exp (-s * (b : ℂ)) =
      (x : ℂ) ^ ρ * (Real.exp (-(19 / 16 : ℝ) * b) : ℂ) := by
    have hc : forwardCoord y x = b := by
      unfold forwardCoord b x
      rw [div_self (pow_pos hy 2).ne', Real.log_one, sub_zero]
    rw [forward_cpow_coord hy (show 0 < x from pow_pos hy 2) ρ, hc, Complex.ofReal_exp,
      Complex.ofReal_mul, Complex.ofReal_neg]
    dsimp only [s, z]
    push_cast
    conv_lhs => rw [← Complex.exp_add]
    conv_rhs => rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  have hc₁ : c * ρ = -(m / ρ) := by
    dsimp only [c]; field_simp [hρ]
  have hc₂ : c * ρ * ρ = -m := by
    dsimp only [c]; field_simp [hρ]
  have hF : F b = -(Real.exp (-(19 / 16 : ℝ) * b) * (m * (x : ℂ) ^ ρ * Q.eval (b : ℂ)).re) := by
    dsimp only [F]
    rw [hc₂, mul_assoc (-m), hz]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hW : (c * ρ * (x : ℂ) ^ ρ).re = -(m * (x : ℂ) ^ ρ / ρ).re := by
    rw [hc₁, neg_mul, Complex.neg_re, div_mul_eq_mul_div]
  have hM :
    (m * (x : ℂ) ^ ρ * (B.eval (b : ℂ) / ρ - Q.eval (b : ℂ))).re =
      gaussianK131Inverse b * (m * (x : ℂ) ^ ρ / ρ).re - (m * (x : ℂ) ^ ρ * Q.eval (b : ℂ)).re := by
    rw [hB, mul_sub, Complex.sub_re]
    congr 1
    rw [show
        m * (x : ℂ) ^ ρ * ((gaussianK131Inverse b : ℂ) / ρ) =
          (gaussianK131Inverse b : ℂ) * (m * (x : ℂ) ^ ρ / ρ)
        by ring]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hK :
    K * Real.exp (-(19 / 16 : ℝ) * b) =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) / y := by
    unfold K b
    rw [mul_assoc, ← Real.exp_add]
    rw [show -(9 / 8 : ℝ) + -(19 / 16 : ℝ) * (9 / 4) = -(27 / 16 : ℝ) * (9 / 4) by norm_num only]
    ring
  change
    (-4) * (gaussianK131UnitWeight / y) * (c * ρ * (x : ℂ) ^ ρ).re + K * (4 * F b - F 0 - 3 * F z) +
        3 * (f 1 * (c * ρ).re - deriv f 1 * c.re) =
      _
  rw [show (9 / 4 : ℂ) = (b : ℂ) by
      unfold b; push_cast; rfl,
    hF, hW, hM]
  change
    (-4) *
          (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4)) *
              gaussianK131Inverse b) /
            y) *
          _ +
        _ +
        _ =
      _
  have he := congrArg (fun t ↦ t * (4 * (m * (x : ℂ) ^ ρ * Q.eval (b : ℂ)).re)) hK
  linear_combination -he

private theorem inverse_low_coeff_zero {j : ℕ} (hj : j < 3) :
    gaussianK131InversePoly.coeff j = 0 := by
  rw [gaussianK131InversePoly, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hd : j ≠ 2 * i.val + 3 := ne_of_lt (hj.trans_le (Nat.le_add_left _ _))
  rw [Polynomial.coeff_monomial]
  simp only [Finsupp.single_apply, Ne.symm hd, ite_false]

/-- The zero-coordinate endpoint starts at the fourth inverse power of
the height, since the first three coefficients of the inverse profile vanish. -/
theorem k131_origin_norm_le {s : ℂ} {h : ℝ} (hh : 0 < h) (hs : h ≤ ‖s‖) :
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    ‖(k131AntiPoly B s).eval 0‖ ≤
      ∑ j ∈ (Finset.range 20).filter (fun j ↦ 3 ≤ j),
        ‖((Polynomial.derivative^[j]) B).eval 0‖ / h ^ (j + 1) := by
  intro B
  refine (k131_anti_norm_le hh hs).trans_eq ?_
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : 3 ≤ j
  · rw [ite_eq_left hj]
  have hz : ((Polynomial.derivative^[j]) B).eval 0 = 0 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, zero_add]
    unfold B
    rw [Polynomial.coeff_map, inverse_low_coeff_zero (lt_of_not_ge hj), map_zero, nsmul_zero]
  rw [ite_eq_right hj, hz, norm_zero, zero_div]

private theorem cutoff_phase_norm {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    ‖((y ^ 2 : ℝ) : ℂ) ^ ρ‖ = y := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (pow_pos hy 2), hr, ← Real.sqrt_eq_rpow,
    Real.sqrt_sq hy.le]

private theorem origin_phase_norm {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hr : ρ.re = 1 / 2) :
    ‖Complex.exp (((9 / 4 + 2 * Real.log y : ℝ) : ℂ) * ρ)‖ = Real.exp (9 / 8) * y := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, hr]
  rw [show (9 / 4 + 2 * Real.log y) * (1 / 2 : ℝ) = 9 / 8 + Real.log y by ring, Real.exp_add,
    Real.exp_log hy]

/-- The K131 spectral coefficient majorant at a positive lower height.
Its cutoff part starts at order two, and its origin part at order four. -/
noncomputable def k131SpectralHeight (h : ℝ) : ℝ :=
  let B := gaussianK131InversePoly.map Complex.ofRealHom
  let D := Polynomial.C (19 / 16 : ℂ) * B - B.derivative
  4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
      (∑ j ∈ Finset.range 20, ‖((Polynomial.derivative^[j]) D).eval (9 / 4)‖ / h ^ (j + 2)) +
    (gaussianK131Amplitude : ℝ) *
      (∑ j ∈ (Finset.range 20).filter (fun j ↦ 3 ≤ j),
        ‖((Polynomial.derivative^[j]) B).eval 0‖ / h ^ (j + 1))

/-- On the critical line the cutoff and zero-coordinate terms, with
their oscillatory phases intact, cost at most the multiplicity times the
height majorant. The coordinate at the physical lower endpoint is separate. -/
theorem k131_spectral_main_le {y h : ℝ} (hy : 0 < y) (hh : 0 < h) {ρ : ℂ} (hr : ρ.re = 1 / 2)
    (hρ : h ≤ |ρ.im|) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ)
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let Q := k131AntiPoly B ((19 / 16 : ℂ) + ρ)
    let z := 9 / 4 + 2 * Real.log y
    let p := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    |(4 * p / y) * ((m : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ ρ * (B.eval (9 / 4) / ρ - Q.eval (9 / 4))).re +
          K * ((m : ℂ) * Complex.exp ((z : ℂ) * ρ) * Q.eval 0).re| ≤
      m * k131SpectralHeight h := by
  intro m B Q z p K
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  have hm : 0 ≤ m := Nat.cast_nonneg _
  have hp : 0 ≤ 4 * p / y :=
    div_nonneg (mul_nonneg (by norm_num only) (mul_nonneg hA (Real.exp_pos _).le)) hy.le
  have hK : 0 ≤ K := mul_nonneg (div_nonneg hA hy.le) (Real.exp_pos _).le
  have hs : h ≤ ‖(19 / 16 : ℂ) + ρ‖ := by
    have he : ((19 / 16 : ℂ) + ρ).im = ρ.im := by
      rw [show (19 / 16 : ℂ) = ((19 / 16 : ℝ) : ℂ) by
          push_cast; rfl,
        Complex.add_im, Complex.ofReal_im, zero_add]
    exact hρ.trans (he ▸ Complex.abs_im_le_norm ((19 / 16 : ℂ) + ρ))
  have hsplit := k131_split_norm_le hh hρ
  have horigin := k131_origin_norm_le hh hs
  dsimp only at hsplit horigin
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg hp, abs_mul, abs_of_nonneg hK]
  have hc :=
    Complex.abs_re_le_norm ((m : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ ρ * (B.eval (9 / 4) / ρ - Q.eval (9 / 4)))
  have ho := Complex.abs_re_le_norm ((m : ℂ) * Complex.exp ((z : ℂ) * ρ) * Q.eval 0)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm,
    cutoff_phase_norm hy hr] at hc
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm,
    origin_phase_norm hy hr] at ho
  have hc' :=
    mul_le_mul_of_nonneg_left (hc.trans (mul_le_mul_of_nonneg_left hsplit (mul_nonneg hm hy.le))) hp
  have ho' :=
    mul_le_mul_of_nonneg_left
      (ho.trans
        (mul_le_mul_of_nonneg_left horigin (mul_nonneg hm (mul_nonneg (Real.exp_pos _).le hy.le))))
      hK
  refine (add_le_add hc' ho').trans_eq ?_
  dsimp only [p, K, k131SpectralHeight]
  rw [Real.exp_neg]
  field_simp [hy.ne', (Real.exp_pos (9 / 8 : ℝ)).ne']

/-- The three physical-lower-end terms in the actual zeta contribution
combine to an inverse-square zero factor multiplying a single antiderivative. -/
theorem k131_zeta_lower_eq {y : ℝ} (hy : 0 < y) {ρ : ℂ} (hρ : ρ ≠ 0) (hs : (19 / 16 : ℂ) + ρ ≠ 0) :
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let c := -m / ρ ^ 2
    let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let d : ℂ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    let s := d + ρ
    let Q := k131AntiPoly B s
    let F :=
      (c * ρ * ρ * Complex.exp ((z : ℂ) * ρ) * Complex.exp (-s * (z : ℂ)) * Q.eval (z : ℂ)).re
    (-3) * K * F + 3 * (f 1 * (c * ρ).re - deriv f 1 * c.re) =
      3 * (K * Real.exp (-(19 / 16 : ℝ) * z)) *
        (m * ((k131AntiPoly (Polynomial.C d * D - D.derivative) s).eval (z : ℂ) / ρ ^ 2)).re := by
  intro z f m c K B d D s Q F
  have hB : B.natDegree < 20 := Polynomial.natDegree_map_le.trans_lt forward_inverse_degree
  have hz : forwardCoord y 1 = z := by
    unfold forwardCoord z
    rw [one_div, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hf : f 1 = K * (Real.exp (-(19 / 16 : ℝ) * z) * gaussianK131Inverse z) := by
    change k131ForwardWeight y 1 = _
    rw [forward_weight_profile hy zero_lt_one, hz]
    rfl
  have hD :
    D.eval (z : ℂ) =
      (((19 / 16 : ℝ) * gaussianK131Inverse z - gaussianK131InversePoly.derivative.eval z : ℝ) :
        ℂ) := by
    have hcast (P : Polynomial ℝ) :
      (P.map Complex.ofRealHom).eval (z : ℂ) = ((P.eval z : ℝ) : ℂ) := by
      rw [Polynomial.eval_map]
      exact Polynomial.eval₂_hom Complex.ofRealHom z
    unfold D B d
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.derivative_map,
      hcast, hcast, gaussian_k131_inverse_eval]
    push_cast
    rfl
  have hP : deriv f 1 = K * (Real.exp (-(19 / 16 : ℝ) * z) * (D.eval (z : ℂ)).re) := by
    have h := forward_log_slope_eval hy (show (0 : ℝ) < 1 from zero_lt_one)
    dsimp only at h
    rw [one_mul, hz] at h
    simpa only [hD, Complex.ofReal_re] using h
  have hBc : B.eval (z : ℂ) = (gaussianK131Inverse z : ℂ) := by
    unfold B
    rw [Polynomial.eval_map]
    change gaussianK131InversePoly.eval₂ Complex.ofRealHom (Complex.ofRealHom z) = _
    rw [Polynomial.eval₂_hom, gaussian_k131_inverse_eval]
    rfl
  have hc₁ : c * ρ = -(m / ρ) := by
    dsimp only [c]; field_simp [hρ]
  have hc₂ : c * ρ * ρ = -m := by
    dsimp only [c]; field_simp [hρ]
  have hphase :
    Complex.exp ((z : ℂ) * ρ) * Complex.exp (-s * (z : ℂ)) =
      (Real.exp (-(19 / 16 : ℝ) * z) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    dsimp only [s, d]
    push_cast
    congr 1
    ring
  have hF : F = -(Real.exp (-(19 / 16 : ℝ) * z) * (m * Q.eval (z : ℂ)).re) := by
    dsimp only [F]
    rw [hc₂, mul_assoc (-m), hphase]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have he := k131_lower_cancel hB (v := (z : ℂ)) hρ hs
  change Q.eval (z : ℂ) - B.eval (z : ℂ) / ρ + D.eval (z : ℂ) / ρ ^ 2 = _ at he
  rw [← he, hf, hP, hF, hc₁]
  have hh :
    m * (Q.eval (z : ℂ) - B.eval (z : ℂ) / ρ + D.eval (z : ℂ) / ρ ^ 2) =
      m * Q.eval (z : ℂ) - B.eval (z : ℂ) * (m / ρ) + D.eval (z : ℂ) * (m / ρ ^ 2) := by
    ring
  rw [hh, hBc, hD]
  dsimp only [c]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, neg_div, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private noncomputable def signedRemainderPoly : Polynomial ℝ :=
  let B := gaussianK131InversePoly
  Polynomial.C ((19 / 16 : ℝ) ^ 2) * B - Polynomial.C (2 * (19 / 16 : ℝ)) * B.derivative +
    B.derivative.derivative

private theorem signed_remainder_coeff_le (j : ℕ) :
    |signedRemainderPoly.coeff j| ≤ k131RemainderPoly.coeff j := by
  simp only [signedRemainderPoly, k131RemainderPoly, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul]
  have hB := forward_inverse_coeff_nonneg j
  have hD := forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg j
  have hDD := forward_deriv_coeff_nonneg (forward_deriv_coeff_nonneg forward_inverse_coeff_nonneg) j
  exact abs_le.mpr ⟨by linarith only [hB, hDD], by linarith only [hD]⟩

private theorem iterated_signed_coeff_le (j n : ℕ) :
    |((Polynomial.derivative^[j]) signedRemainderPoly).coeff n| ≤
      ((Polynomial.derivative^[j]) k131RemainderPoly).coeff n := by
  simp only [Polynomial.coeff_iterate_derivative, nsmul_eq_mul, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) ((n + j).descFactorial j))]
  exact mul_le_mul_of_nonneg_left (signed_remainder_coeff_le _) (Nat.cast_nonneg _)

private theorem eval_abs_le_of_coeff {P G : Polynomial ℝ} (h : ∀ n, |P.coeff n| ≤ G.coeff n) {z : ℝ}
    (hz : 0 ≤ z) : |P.eval z| ≤ G.eval z := by
  let N := max P.natDegree G.natDegree + 1
  have hP : P.natDegree < N := Nat.lt_succ_of_le (le_max_left _ _)
  have hG : G.natDegree < N := Nat.lt_succ_of_le (le_max_right _ _)
  rw [Polynomial.eval_eq_sum_range' hP, Polynomial.eval_eq_sum_range' hG]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (pow_nonneg hz n)]
  exact mul_le_mul_of_nonneg_right (h n) (pow_nonneg hz n)

private theorem signed_remainder_map :
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let d : ℂ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    Polynomial.C d * D - D.derivative = signedRemainderPoly.map Complex.ofRealHom := by
  intro B d D
  have h₁ : Complex.ofRealHom ((19 / 16 : ℝ) ^ 2) = d ^ 2 := by
    change ((((19 / 16 : ℝ) ^ 2 : ℝ) : ℂ)) = (19 / 16 : ℂ) ^ 2
    push_cast
    ring
  have h₂ : Complex.ofRealHom (2 * (19 / 16 : ℝ)) = 2 * d := by
    change ((2 * (19 / 16 : ℝ) : ℝ) : ℂ) = 2 * (19 / 16 : ℂ)
    push_cast
    ring
  unfold signedRemainderPoly
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C,
    ← Polynomial.derivative_map]
  rw [h₁, h₂, map_pow, map_mul, map_ofNat]
  dsimp only [D, B]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul]
  ring

/-- At a nonnegative logarithmic coordinate, the signed lower-endpoint
antiderivative is dominated by the real remainder polynomial's antiderivative. -/
theorem k131_lower_antideriv_le {z : ℝ} (hz : 0 ≤ z) {s : ℂ} (hs : (19 / 16 : ℝ) ≤ ‖s‖) :
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let d : ℂ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    ‖(k131AntiPoly (Polynomial.C d * D - D.derivative) s).eval (z : ℂ)‖ ≤
      (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z := by
  intro B d D
  rw [show Polynomial.C d * D - D.derivative = signedRemainderPoly.map Complex.ofRealHom from
      signed_remainder_map]
  refine (k131_anti_norm_le (by norm_num only : (0 : ℝ) < 19 / 16) hs).trans ?_
  rw [real_anti_poly]
  simp only [k131AntiPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_le_sum
  intro j _
  rw [Polynomial.iterate_derivative_map, Polynomial.eval_map]
  change
    ‖((Polynomial.derivative^[j]) signedRemainderPoly).eval₂ Complex.ofRealHom
            (Complex.ofRealHom z)‖ /
        _ ≤
      _
  rw [Polynomial.eval₂_hom]
  change ‖((((Polynomial.derivative^[j]) signedRemainderPoly).eval z : ℝ) : ℂ)‖ / _ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs, ← div_eq_inv_mul]
  exact
    div_le_div_of_nonneg_right (eval_abs_le_of_coeff (iterated_signed_coeff_le j) hz)
      (pow_nonneg (by norm_num only) _)

/-- The physical lower endpoint costs at most the positive remainder
antiderivative times the multiplicity-weighted inverse square of the zero. -/
theorem k131_lower_term_le {z : ℝ} (hz : 0 ≤ z) {ρ : ℂ} (hre : 0 ≤ ρ.re) (m : ℕ) :
    let B := gaussianK131InversePoly.map Complex.ofRealHom
    let d : ℂ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    |((m : ℂ) *
            ((k131AntiPoly (Polynomial.C d * D - D.derivative) (d + ρ)).eval (z : ℂ) / ρ ^ 2)).re| ≤
      (m : ℝ) / ‖ρ‖ ^ 2 * (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z := by
  intro B d D
  have hd : d = ((19 / 16 : ℝ) : ℂ) := by
    unfold d; push_cast; rfl
  have hs : (19 / 16 : ℝ) ≤ ‖d + ρ‖ := by
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [hd, Complex.add_re, Complex.ofReal_re, abs_of_nonneg (by linarith only [hre])]
    linarith only [hre]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
  calc
    _ =
        ((m : ℝ) / ‖ρ‖ ^ 2) *
          ‖(k131AntiPoly (Polynomial.C d * D - D.derivative) (d + ρ)).eval (z : ℂ)‖ :=
      by ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (k131_lower_antideriv_le hz hs)
        (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- The coefficient multiplying the inverse-square zero mass in the
physical-endpoint correction. -/
noncomputable def k131LowerMass (y : ℝ) : ℝ :=
  3 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ)) *
    (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval (9 / 4 + 2 * Real.log y)

/-- A critical-line zero costs its height majorant and its share of the
physical-endpoint correction, with multiplicity included in both terms. -/
theorem k131_zeta_endpoint_le {y h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) {ρ : ℂ} (hr : ρ.re = 1 / 2)
    (hρ : h ≤ |ρ.im|) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ)
    |k131ZetaEndpoint y ρ| ≤ m * k131SpectralHeight h + k131LowerMass y * (m / ‖ρ‖ ^ 2) := by
  intro m
  have hy0 := zero_lt_one.trans_le hy
  have hne := norm_pos_iff.mp (hh.trans_le (hρ.trans (Complex.abs_im_le_norm ρ)))
  have hs : (19 / 16 : ℂ) + ρ ≠ 0 := by
    intro he
    have hz := congrArg Complex.im he
    rw [show (19 / 16 : ℂ) = ((19 / 16 : ℝ) : ℂ) by
        push_cast; rfl,
      Complex.add_im, Complex.ofReal_im, zero_add, Complex.zero_im] at hz
    rw [hz, abs_zero] at hρ
    exact (not_lt_of_ge hρ) hh
  have hmain := k131_spectral_main_le hy0 hh hr hρ
  have hsplit := k131_zeta_split_eq hy0 hne
  have hlower := k131_zeta_lower_eq hy0 hne hs
  dsimp only at hmain hsplit hlower
  let z := 9 / 4 + 2 * Real.log y
  let B := gaussianK131InversePoly.map Complex.ofRealHom
  let d : ℂ := 19 / 16
  let D := Polynomial.C d * B - B.derivative
  let A := (k131AntiPoly (Polynomial.C d * D - D.derivative) (d + ρ)).eval (z : ℂ)
  let J := ((m : ℂ) * (A / ρ ^ 2)).re
  let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
  let R := 3 * (K * Real.exp (-(19 / 16 : ℝ) * z))
  have hc :
    (-(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) / ρ ^ 2) * ρ * ρ =
      -(AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ) := by
    field_simp [hne]
  simp only [hc, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, neg_mul,
    Complex.neg_re] at hsplit hlower
  have hR : 0 ≤ R := by
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact
      mul_nonneg (by norm_num only)
        (mul_nonneg (mul_nonneg (div_nonneg hA hy0.le) (Real.exp_pos _).le) (Real.exp_pos _).le)
  have hJ :=
    k131_lower_term_le
      (show 0 ≤ z by
        unfold z; linarith only [Real.log_nonneg hy])
      (ρ := ρ) (by linarith only [hr])
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ)
  have hRL : R * (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z = k131LowerMass y := by
    have hz : forwardCoord y 1 = z := by
      unfold forwardCoord z
      rw [one_div, Real.log_inv, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      ring
    have he := forward_decay_power hy0 (show (0 : ℝ) < 1 from zero_lt_one)
    rw [hz, Real.one_rpow, mul_one] at he
    unfold R K k131LowerMass k131Prefactor at *
    rw [he]
    dsimp only [z]
    ring
  have hrest : |R * J| ≤ k131LowerMass y * (m / ‖ρ‖ ^ 2) := by
    rw [abs_mul, abs_of_nonneg hR]
    refine (mul_le_mul_of_nonneg_left hJ hR).trans_eq ?_
    rw [← hRL]
    ring
  let M :=
    (4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) / y) *
        ((m : ℂ) * ((y ^ 2 : ℝ) : ℂ) ^ ρ *
            (B.eval (9 / 4) / ρ - (k131AntiPoly B (d + ρ)).eval (9 / 4))).re +
      K * ((m : ℂ) * Complex.exp ((z : ℂ) * ρ) * (k131AntiPoly B (d + ρ)).eval 0).re
  have heq : k131ZetaEndpoint y ρ = M + R * J := by
    dsimp only [M, R, J, A, D, d, B, K, z, m]
    simp only [Complex.ofReal_natCast] at *
    linear_combination (norm := ring_nf) hsplit + hlower
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hmain hrest)

/-- An eventual numerical bound on the finite endpoint sums passes to the
principal spectral correction. -/
theorem k131_spectral_bound_of_sums {y B : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2)
    (hB : ∀ᶠ m in Filter.atTop, |∑ ρ ∈ k131ZeroRect m, k131ZetaEndpoint y ρ| ≤ B) :
    |k131PrincipalSpectral y| ≤ B := by
  exact le_of_tendsto (continuous_abs.continuousAt.tendsto.comp (k131_zeta_endpoint_limit hy hx)) hB

/-- The physical endpoint contributes at most 231/5000 times its remainder
coefficient to the absolute spectral sum over any explicit-formula rectangle. -/
theorem k131_endpoint_sum_le (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) (m : ℕ) (h : ℂ → ℝ)
    (hh : ∀ ρ ∈ k131ZeroRect m, 0 < h ρ ∧ h ρ ≤ |ρ.im|) :
    |∑ ρ ∈ k131ZeroRect m, k131ZetaEndpoint y ρ| ≤
      (∑ ρ ∈ k131ZeroRect m,
          (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
            k131SpectralHeight (h ρ)) +
        (231 / 5000 : ℝ) * k131LowerMass y := by
  let S := k131ZeroRect m
  have hzero (ρ : ℂ) (hρ : ρ ∈ S) : riemannZeta ρ = 0 :=
    (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
        (Finset.mem_filter.mp hρ).1).2
  have hre (ρ : ℂ) (hρ : ρ ∈ S) : 0 ≤ ρ.re := not_lt.mp (Finset.mem_filter.mp hρ).2
  have hmass :=
    AnalyticNumberTheory.RiemannZeta.sum_zetaZeroMultiplicity_invNormSq_le hRH S hzero hre
  simp only [← Complex.sq_norm] at hmass
  have hmass' :
    (∑ ρ ∈ S, (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) / ‖ρ‖ ^ 2) ≤
      231 / 5000 := by
    linarith only [hmass, AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000]
  have hL : 0 ≤ k131LowerMass y := by
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hz : 0 ≤ 9 / 4 + 2 * Real.log y := by linarith only [Real.log_nonneg hy]
    have hs : (19 / 16 : ℝ) ≤ ‖(19 / 16 : ℂ)‖ := by
      rw [show (19 / 16 : ℂ) = ((19 / 16 : ℝ) : ℂ) by
          push_cast; rfl,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num only)]
    have hP := (norm_nonneg _).trans (k131_lower_antideriv_le hz hs)
    exact
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num only) (mul_nonneg hA (Real.exp_pos _).le))
          (Real.rpow_nonneg (zero_le_one.trans hy) _))
        hP
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine
    (Finset.sum_le_sum
          (fun ρ hρ ↦
            k131_zeta_endpoint_le hy (hh ρ hρ).1
              (AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH
                (hzero ρ hρ) (hre ρ hρ))
              (hh ρ hρ).2)).trans
      ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_le_add_right (by simpa only [mul_comm] using mul_le_mul_of_nonneg_left hmass' hL) _

/-- An eventual height certificate for the rectangular sums bounds the
principal spectral term, with the physical endpoint already absorbed. -/
theorem k131_spectral_le_of_heights (hRH : RiemannHypothesis) {y C : ℝ} (hy : 1 < y) (h : ℂ → ℝ)
    (hh : ∀ m ρ, ρ ∈ k131ZeroRect m → 0 < h ρ ∧ h ρ ≤ |ρ.im|)
    (hC :
      ∀ᶠ m in Filter.atTop,
        (∑ ρ ∈ k131ZeroRect m,
            (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
              k131SpectralHeight (h ρ)) ≤
          C) :
    |k131PrincipalSpectral y| ≤ C + (231 / 5000 : ℝ) * k131LowerMass y := by
  have hx : 1 < y ^ 2 := by
    simpa only [one_pow] using
      pow_lt_pow_left₀ hy (show (0 : ℝ) ≤ 1 from zero_le_one) (by decide : (2 : ℕ) ≠ 0)
  apply k131_spectral_bound_of_sums (zero_lt_one.trans hy) hx
  filter_upwards [hC] with m hm
  exact (k131_endpoint_sum_le hRH hy.le m h (hh m)).trans (add_le_add_left hm _)

private theorem scaled_inverse_power_le {a t c : ℝ} (ha : 0 < a) (hat : a ≤ t) (hc : 0 ≤ c)
    (j : ℕ) : t ^ 2 * (c / t ^ (j + 2)) ≤ a ^ 2 * (c / a ^ (j + 2)) := by
  have he {v : ℝ} (hv : 0 < v) : v ^ 2 * (c / v ^ (j + 2)) = c / v ^ j := by
    rw [pow_add]
    field_simp [hv.ne']
  rw [he (ha.trans_le hat), he ha]
  exact div_le_div_of_nonneg_left hc (pow_pos ha _) (pow_le_pow_left₀ ha.le hat _)

/-- The spectral height majorant multiplied by height squared decreases on
positive heights. This retains the inverse-square tail factor above 100. -/
theorem k131_scaled_height_le {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    t ^ 2 * k131SpectralHeight t ≤ a ^ 2 * k131SpectralHeight a := by
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  unfold k131SpectralHeight
  simp only [mul_add, mul_left_comm (_ ^ 2), Finset.mul_sum]
  apply add_le_add
  · apply Finset.sum_le_sum
    intro j _
    exact
      mul_le_mul_of_nonneg_left (scaled_inverse_power_le ha hat (norm_nonneg _) j)
        (mul_nonneg (by norm_num only) (mul_nonneg hA (Real.exp_pos _).le))
  · apply Finset.sum_le_sum
    intro j hj
    apply mul_le_mul_of_nonneg_left _ hA
    have hJ : 3 ≤ j := (Finset.mem_filter.mp hj).2
    rw [show j + 1 = (j - 1) + 2 from
        (congrArg (fun k ↦ k + 1) (Nat.sub_add_cancel ((by decide : 1 ≤ 3).trans hJ))).symm]
    exact scaled_inverse_power_le ha hat (norm_nonneg _) (j - 1)

/-- The tail of the K131 height majorant above 100 uses the certified
two-sided inverse-square ordinate tail. -/
theorem k131_height_tail_le (hRH : RiemannHypothesis) (S : Finset ℂ)
    (hz : ∀ ρ ∈ S, riemannZeta ρ = 0) (hre : ∀ ρ ∈ S, 0 ≤ ρ.re) (hhi : ∀ ρ ∈ S, 100 < |ρ.im|) :
    (∑ ρ ∈ S,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          k131SpectralHeight |ρ.im|) ≤
      (100 : ℝ) ^ 2 * k131SpectralHeight 100 * (13 / 1000 : ℝ) := by
  let H := (100 : ℝ) ^ 2 * k131SpectralHeight 100
  have hH : 0 ≤ H := by
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    unfold H k131SpectralHeight
    positivity
  have htail :=
    (AnalyticNumberTheory.RiemannZeta.finite_ordinate_tail_le hRH S 100 hz hre hhi).trans
      (AnalyticNumberTheory.RiemannZeta.ordinateTail_hundred_le hRH)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left htail hH)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hp : 0 < |ρ.im| := (by norm_num only : (0 : ℝ) < 100).trans (hhi ρ hρ)
  have h := k131_scaled_height_le (by norm_num only : (0 : ℝ) < 100) (hhi ρ hρ).le
  have hb : k131SpectralHeight |ρ.im| ≤ H / |ρ.im| ^ 2 := by
    apply (le_div_iff₀ (pow_pos hp 2)).mpr
    simpa only [mul_comm] using h
  refine (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)).trans_eq ?_
  ring

private theorem height_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ k131SpectralHeight t := by
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
    rw [k131_amplitude_eq]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
  unfold k131SpectralHeight
  positivity

private theorem height_mono {a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    k131SpectralHeight t ≤ k131SpectralHeight a := by
  have h := k131_scaled_height_le ha hat
  have hs := pow_le_pow_left₀ ha.le hat 2
  exact
    le_of_mul_le_mul_left
      ((mul_le_mul_of_nonneg_right hs (height_nonneg (ha.le.trans hat))).trans h) (pow_pos ha 2)

/-- The sum of the two-sided height majorants at the 29 certified
rational lower endpoints. The underlying bracket data stay private. -/
noncomputable def k131HeadHeight : ℝ :=
  2 * ∑ i : Fin 29, k131SpectralHeight (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i : ℝ)

/-- The low zero ledger through height 100 is bounded by the two-sided
height majorant at the certified lower endpoints. -/
theorem k131_height_head_le (hRH : RiemannHypothesis) :
    (∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100,
        (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          k131SpectralHeight |ρ.im|) ≤
      k131HeadHeight := by
  obtain ⟨g, hm, hp, hu, hz, hl, _⟩ := AnalyticNumberTheory.RiemannZeta.low_zero_100_exists
  have hcomplete :=
    AnalyticNumberTheory.RiemannZeta.critical_zeros_complete_simple hRH
      (AnalyticNumberTheory.RiemannZeta.count_100_eq_58_of_RH hRH).le g hm hp hu hz
  let Z := fun i ↦ ((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I
  let F := fun ρ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * k131SpectralHeight |ρ.im|
  have hconj :
    ∀ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100, F ((starRingEnd ℂ) ρ) = F ρ := by
    intro ρ hρ
    have hzero :=
      (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mp hρ
    have hr :=
      AnalyticNumberTheory.RiemannZeta.zeta_zero_re_eq_half_of_riemannHypothesis hRH hzero.1
        hzero.2.1
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_re] at hr
      norm_num only at hr
    simp only [F, AnalyticNumberTheory.RiemannZeta.multiplicity_conj hne, Complex.conj_im, abs_neg]
  change (∑ ρ ∈ _, F ρ) ≤ _
  rw [AnalyticNumberTheory.RiemannZeta.zero_sum_eq_two_positive hRH
      (by norm_num only : (0 : ℝ) ≤ 100) F hconj]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  refine
    (Finset.sum_le_sum_of_subset_of_nonneg hcomplete.1
          (fun ρ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (height_nonneg (abs_nonneg _)))).trans
      ?_
  rw [Finset.sum_image
      (fun i _ j _ hij ↦
        AnalyticNumberTheory.RiemannZeta.critical_points_injective g hm.injective hij)]
  apply Finset.sum_le_sum
  intro i _
  have he : (Z i).im = g i := by
    simp only [Z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  change F (Z i) ≤ _
  simp only [F, he, abs_of_pos (hp i),
    show AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity (Z i) = 1 from hcomplete.2 i,
    Nat.cast_one, one_mul]
  have hpos : ∀ i : Fin 29, 0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
    decide +kernel
  exact height_mono (Rat.cast_pos.mpr (hpos i)) (hl i)

/-- The full principal spectral correction uses the low-zero certificate,
the strict high tail and the already bounded physical-endpoint remainder. -/
theorem k131_spectral_head_tail_le (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 < y) :
    |k131PrincipalSpectral y| ≤
      (k131HeadHeight + (100 : ℝ) ^ 2 * k131SpectralHeight 100 * (13 / 1000)) +
        (231 / 5000 : ℝ) * k131LowerMass y := by
  let h := fun ρ : ℂ ↦ |ρ.im|
  have hz {m : ℕ} {ρ : ℂ} (hρ : ρ ∈ k131ZeroRect m) : riemannZeta ρ = 0 :=
    (AnalyticNumberTheory.RiemannZeta.mem_riemannZetaZerosInAnyRectangle_iff.mp
        (Finset.mem_filter.mp hρ).1).2
  have hr {m : ℕ} {ρ : ℂ} (hρ : ρ ∈ k131ZeroRect m) : 0 ≤ ρ.re :=
    not_lt.mp (Finset.mem_filter.mp hρ).2
  apply k131_spectral_le_of_heights hRH hy h
  · intro m ρ hρ
    exact
      ⟨(mul_pos (by norm_num only) Real.pi_pos).trans
          (AnalyticNumberTheory.RiemannZeta.zero_height_gt_two_pi hRH (hz hρ) (hr hρ)),
        le_rfl⟩
  filter_upwards with m
  let F := fun ρ ↦
    (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) * k131SpectralHeight |ρ.im|
  let p := fun ρ : ℂ ↦ |ρ.im| ≤ 100
  change (∑ ρ ∈ k131ZeroRect m, F ρ) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not (k131ZeroRect m) p F]
  apply add_le_add
  · have hsub : (k131ZeroRect m).filter p ⊆ AnalyticNumberTheory.RiemannZeta.zerosUpTo 100 := by
      intro ρ hρ
      have hq := Finset.mem_filter.mp hρ
      exact
        (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo (by norm_num only : (0 : ℝ) ≤ 100)).mpr
          ⟨hz hq.1, hr hq.1, hq.2⟩
    exact
      (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun ρ _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (height_nonneg (abs_nonneg _)))).trans
        (k131_height_head_le hRH)
  · exact
      k131_height_tail_le hRH _ (fun _ hρ ↦ hz (Finset.mem_filter.mp hρ).1)
        (fun _ hρ ↦ hr (Finset.mem_filter.mp hρ).1)
        (fun _ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)

private def inverseDerivRat (j : ℕ) (v : ℚ) : ℚ :=
  ∑ i : Fin 9, inverseCoeffs i * (((2 * i.val + 3).descFactorial j : ℚ) * v ^ (2 * i.val + 3 - j))

private theorem inverse_deriv_rat_cast (j : ℕ) (v : ℚ) :
    ((Polynomial.derivative^[j]) gaussianK131InversePoly).eval (v : ℝ) =
      (inverseDerivRat j v : ℝ) := by
  rw [eval_iterate_inverse]
  simp only [inverseDerivRat, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow]

private def spectralHeightRat (h : ℚ) : ℚ :=
  4 * (gaussianK131Amplitude * (224408 / 10000000)) *
      (∑ j ∈ Finset.range 20,
        |(19 / 16 : ℚ) * inverseDerivRat j (9 / 4) - inverseDerivRat (j + 1) (9 / 4)| /
          h ^ (j + 2)) +
    gaussianK131Amplitude *
      (∑ j ∈ (Finset.range 20).filter (fun j ↦ 3 ≤ j), |inverseDerivRat j 0| / h ^ (j + 1))

private theorem height_rat_upper {h : ℚ} (hh : 0 < h) :
    k131SpectralHeight (h : ℝ) ≤ (spectralHeightRat h : ℝ) := by
  let B := gaussianK131InversePoly
  let d : ℝ := 19 / 16
  let D := Polynomial.C d * B - B.derivative
  have hmap (P : Polynomial ℝ) (j : ℕ) (v : ℝ) :
    ‖((Polynomial.derivative^[j]) (P.map Complex.ofRealHom)).eval (v : ℂ)‖ =
      |((Polynomial.derivative^[j]) P).eval v| := by
    rw [Polynomial.iterate_derivative_map, Polynomial.eval_map]
    change ‖((Polynomial.derivative^[j]) P).eval₂ Complex.ofRealHom (Complex.ofRealHom v)‖ = _
    rw [Polynomial.eval₂_hom]
    exact (Complex.norm_real _).trans (Real.norm_eq_abs _)
  have hD :
    Polynomial.C (19 / 16 : ℂ) * B.map Complex.ofRealHom - (B.map Complex.ofRealHom).derivative =
      D.map Complex.ofRealHom := by
    unfold D d
    simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.derivative_map]
    change Polynomial.C (19 / 16 : ℂ) * _ - _ = Polynomial.C ((19 / 16 : ℝ) : ℂ) * _ - _
    push_cast
    rfl
  have he (j : ℕ) (v : ℚ) :
    ((Polynomial.derivative^[j]) D).eval (v : ℝ) =
      ((19 / 16 : ℚ) * inverseDerivRat j v - inverseDerivRat (j + 1) v : ℚ) := by
    unfold D d B
    rw [Polynomial.iterate_derivative_sub, Polynomial.iterate_derivative_C_mul, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_C, ← Function.iterate_succ_apply, inverse_deriv_rat_cast,
      inverse_deriv_rat_cast]
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  unfold k131SpectralHeight spectralHeightRat
  dsimp only at *
  rw [hD]
  simp only [Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sum,
    Rat.cast_abs, Rat.cast_pow]
  apply add_le_add
  · have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have he' (j : ℕ) :
      ‖((Polynomial.derivative^[j]) (D.map Complex.ofRealHom)).eval (9 / 4)‖ =
        |(19 / 16 : ℝ) * (inverseDerivRat j (9 / 4) : ℝ) -
            (inverseDerivRat (j + 1) (9 / 4) : ℝ)| := by
      rw [show (9 / 4 : ℂ) = ((9 / 4 : ℝ) : ℂ) by
          push_cast; rfl,
        hmap]
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_mul] using
        congrArg abs (he j (9 / 4))
    simp only [he']
    apply mul_le_mul_of_nonneg_right
    · exact
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left exp_edge_upper hA) (by norm_num only)
    · exact
        Finset.sum_nonneg fun _ _ ↦
          div_nonneg (abs_nonneg _) (pow_nonneg (Rat.cast_nonneg.mpr hh.le) _)
  · apply le_of_eq
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from Complex.ofReal_zero.symm, hmap,
      show (0 : ℝ) = ((0 : ℚ) : ℝ) from Rat.cast_zero.symm, inverse_deriv_rat_cast]

private theorem spectral_rat_certificate :
    2 * (∑ i : Fin 29, spectralHeightRat (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i)) +
        130 * spectralHeightRat 100 ≤
      (25329 / 1000000 : ℚ) := by
  decide +kernel

/-- The certified low-zero sum and the two-sided tail fit within the
spectral constant of the K131 comparison. -/
theorem k131_spectral_height_budget :
    k131HeadHeight + (100 : ℝ) ^ 2 * k131SpectralHeight 100 * (13 / 1000) ≤ 25329 / 1000000 := by
  have hpos : ∀ i : Fin 29, 0 < AnalyticNumberTheory.RiemannZeta.lowZero100Lower i := by
    decide +kernel
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ height_rat_upper (hpos i))
  have ht := height_rat_upper (show (0 : ℚ) < 100 by decide)
  have hc := (Rat.cast_le (K := ℝ)).mpr spectral_rat_certificate
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] at hc ht
  unfold k131HeadHeight
  linarith only [hp, ht, hc]

/-- Under RH, the principal spectral contribution satisfies the numerical
K131 budget, plus the explicitly separated physical-endpoint correction. -/
theorem k131_principal_spectral_le (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 < y) :
    |k131PrincipalSpectral y| ≤ 25329 / 1000000 + (231 / 5000 : ℝ) * k131LowerMass y := by
  exact (k131_spectral_head_tail_le hRH hy).trans (add_le_add_left k131_spectral_height_budget _)

/-- The principal Mangoldt combination is bounded below by its linear
term, cutoff term, nontrivial-zero term and the corrections at 1,
with the explicit trivial-zero allowance subtracted. -/
theorem k131_principal_explicit_lower {y : ℝ} (hy : 0 < y) (hx : 1 < y ^ 2) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let P := fun t ↦ t * deriv f t
    let w := fun n : ℕ ↦ f n * ArithmeticFunction.vonMangoldt n
    let c := Real.log (2 * Real.pi)
    let C := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
    let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
    let B :=
      3 * ((5 / 12 : ℝ) / (2 - 19 / 16)) *
          ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
          y ^ (-(27 / 8 : ℝ)) *
          k131RemainderPoly.eval z +
        gaussianK131EdgeLoss / y ^ 5
    k131PrincipalDelta * y -
            3 * (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) *
              Q.eval z +
          4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x + c) +
          3 * (1 - c) * f 1 +
          3 * (C - 1) * P 1 +
          k131PrincipalSpectral y -
        B ≤
      4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) := by
  intro x u z f P w c C Q B
  have hx' : 1 ≤ x := hx.le
  have hxu : x ≤ u := le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only))
  have h := k131_principal_centered hy hx.le c
  dsimp only at h
  rw [k131_principal_mass_eval hy hx.le] at h
  have h₁ := principal_error_split hy le_rfl hx'
  have h₂ := principal_error_split hy hx' hxu
  dsimp only at h₁ h₂
  dsimp only [x, u, c] at h₁ h₂
  rw [h₁, h₂] at h
  have hP : P u = 0 := by
    change u * deriv (k131ForwardWeight y) (y ^ 2 * Real.exp (9 / 4)) = 0
    rw [forward_slope_right hy, mul_zero]
  have hE := k131_centered_trivial_part hx
  have hT := k131_trivial_remainder_le hy hx
  dsimp only at hT
  have hT' := (abs_le.mp hT).1
  dsimp only [x, u, z, f, P, w, c, C, Q, B, k131PrincipalSpectral] at hP ⊢
  rw [hP] at h
  linarith only [h, hT',
    congrArg (fun t ↦ 4 * (y ^ 2 * deriv (k131ForwardWeight y) (y ^ 2)) * t) hE]

/-- The explicit lower-endpoint terms left by integrating the principal
formula from 1, before conversion to the manuscript remainder polynomial. -/
noncomputable def k131PrincipalCutoff (y : ℝ) : ℝ :=
  let z := 9 / 4 + 2 * Real.log y
  let c := Real.log (2 * Real.pi)
  let C := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
  let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
  (-3) * (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) *
      Q.eval z +
    3 * (1 - c) * k131ForwardWeight y 1 +
    3 * (C - 1) * deriv (k131ForwardWeight y) 1

private theorem signed_remainder_real (d : ℝ) (B : Polynomial ℝ) :
    let D := Polynomial.C d * B - B.derivative
    Polynomial.C d * D - D.derivative =
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative := by
  intro D
  dsimp only [D]
  rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul, map_pow, map_mul, map_ofNat]
  ring

/-- The deterministic cutoff expression has the two manuscript
antiderivatives and the logarithmic correction. -/
theorem k131_cutoff_poly_eq {v : ℝ} :
    let d : ℝ := 19 / 16
    let B := gaussianK131InversePoly
    let D := Polynomial.C d * B - B.derivative
    let Q := k131MomentPoly B (35 / 16) 0
    Q.eval v + D.eval v - B.eval v =
      (k131MomentPoly
            (Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative +
              B.derivative.derivative)
            (35 / 16) 0).eval
        v := by
  intro d B D Q
  have hB : B.natDegree < 20 := forward_inverse_degree
  have hD : D.natDegree < 20 :=
    ((Polynomial.natDegree_sub_le _ _).trans
          (max_le (Polynomial.natDegree_C_mul_le _ _)
            ((Polynomial.natDegree_derivative_le B).trans (Nat.sub_le _ _)))).trans_lt
      hB
  have hd : (35 / 16 : ℝ) = d + 1 := by
    unfold d; norm_num only
  have ha := moment_poly_deriv hB (by norm_num only : (35 / 16 : ℝ) ≠ 0) v
  have hb := moment_poly_deriv hD (by norm_num only : (35 / 16 : ℝ) ≠ 0) v
  have h₁ := anti_difference_eval B d (35 / 16) v
  have h₂ := anti_difference_eval D d (35 / 16) v
  change (k131AntiPoly D (35 / 16)).eval v = _ at h₁
  rw [show
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative =
        Polynomial.C d * D - D.derivative
      from (signed_remainder_real d B).symm,
    real_anti_poly, h₂]
  change (k131MomentPoly B (35 / 16) 0).eval v + D.eval v - B.eval v = _
  rw [real_anti_poly]
  linarith only [ha, hb, h₁]

private theorem cutoff_scale_eq {y : ℝ} (hy : 0 < y) :
    let z := 9 / 4 + 2 * Real.log y
    (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) =
      ((gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))) *
        Real.exp (-(19 / 16 : ℝ) * z) := by
  intro z
  have h :
    Real.exp (Real.log y) * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) =
      (Real.exp (Real.log y))⁻¹ * Real.exp (-(9 / 8 : ℝ)) * Real.exp (-(19 / 16 : ℝ) * z) := by
    rw [← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  rw [Real.exp_log hy] at h
  rw [div_eq_mul_inv]
  linear_combination (norm := ring_nf) (gaussianK131Amplitude : ℝ) * h

/-- The deterministic cutoff separates the logarithmic correction and
the signed remainder polynomial evaluated at the two real rates. -/
theorem k131_principal_cutoff_eq {y : ℝ} (hy : 0 < y) :
    let z := 9 / 4 + 2 * Real.log y
    let B := gaussianK131InversePoly
    let d : ℝ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    let Q :=
      Polynomial.C (d ^ 2) * B - Polynomial.C (2 * d) * B.derivative + B.derivative.derivative
    let c := Real.log (2 * Real.pi)
    let C := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
    k131PrincipalCutoff y =
      3 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
        y ^ (-(27 / 8 : ℝ)) *
        (-(k131MomentPoly Q (35 / 16) 0).eval z - c * B.eval z + C * D.eval z) := by
  intro z B d D Q c C
  let K := (gaussianK131Amplitude : ℝ) / y * Real.exp (-(9 / 8 : ℝ))
  have hz : forwardCoord y 1 = z := by
    unfold forwardCoord z
    rw [one_div, Real.log_inv, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    ring
  have hf : k131ForwardWeight y 1 = K * (Real.exp (-d * z) * B.eval z) := by
    rw [forward_weight_profile hy zero_lt_one, hz]
    unfold B recoveryProfile
    rw [gaussian_k131_inverse_eval]
  have hp : deriv (k131ForwardWeight y) 1 = K * (Real.exp (-d * z) * D.eval z) := by
    have h := forward_log_slope_eval hy (show (0 : ℝ) < 1 from zero_lt_one)
    dsimp only at h
    rw [one_mul, hz] at h
    unfold D B
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      gaussian_k131_inverse_eval] using h
  have hd := forward_decay_power hy (show (0 : ℝ) < 1 from zero_lt_one)
  rw [hz, Real.one_rpow, mul_one] at hd
  have hscale := cutoff_scale_eq hy
  dsimp only at hscale
  have he := k131_cutoff_poly_eq (v := z)
  change (k131MomentPoly B (35 / 16) 0).eval z + D.eval z - B.eval z = _ at he
  change _ = (k131MomentPoly Q (35 / 16) 0).eval z at he
  unfold k131PrincipalCutoff
  dsimp only
  rw [hf, hp]
  change
    (-3) * (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) *
          (k131MomentPoly B (35 / 16) 0).eval z +
        3 * (1 - c) * (K * (Real.exp (-d * z) * B.eval z)) +
        3 * (C - 1) * (K * (Real.exp (-d * z) * D.eval z)) =
      _
  rw [← he]
  change
    (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * z) =
      K * Real.exp (-d * z) at hscale
  change
    K * Real.exp (-d * z) =
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
        y ^ (-(27 / 8 : ℝ)) at hd
  let M := (k131MomentPoly B (35 / 16) 0).eval z
  linear_combination (norm := (dsimp only [M]; ring_nf))
    -3 * M * hscale + 3 * (-M + (1 - c) * B.eval z + (C - 1) * D.eval z) * hd

private theorem cutoff_zeta_constant_abs (hRH : RiemannHypothesis) :
    |AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re| ≤
      (16 / 25 : ℝ) := by
  have h := AnalyticNumberTheory.RiemannXi.deriv_logDeriv_riemannXi_zero_eq
  have he : (-1 + (Real.pi : ℂ) ^ 2 / 24 : ℂ) = ((-1 + Real.pi ^ 2 / 24 : ℝ) : ℂ) := by
    push_cast; rfl
  rw [he] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  have hn :=
    (Complex.abs_re_le_norm _).trans
      (AnalyticNumberTheory.RiemannXi.norm_deriv_logDeriv_zero_le_two_mass_RH hRH)
  have hl := (abs_le.mp hn).1
  have hu := (abs_le.mp hn).2
  have hpi : (31415 / 10000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d4]
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 31415 / 10000) hpi 2
  have hq := pow_le_pow_left₀ Real.pi_pos.le Real.pi_lt_four.le 2
  have hm := AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_231_div_10000
  exact abs_le.mpr ⟨by linarith only [hl, hr, hq, hm], by linarith only [hu, hr, hp, hm]⟩

private theorem cutoff_signed_moment_le {s z : ℝ} (hs : 19 / 16 ≤ s) (hz : 0 ≤ z) :
    |(k131MomentPoly signedRemainderPoly s 0).eval z| ≤
      (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z := by
  simp only [real_anti_poly, k131AntiPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  have hp : 0 < (19 / 16 : ℝ) := by norm_num only
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (hp.le.trans hs) _)), ← div_eq_inv_mul, ←
    div_eq_inv_mul]
  have he := eval_abs_le_of_coeff (iterated_signed_coeff_le j) hz
  exact
    (div_le_div_of_nonneg_right he (pow_nonneg (hp.le.trans hs) _)).trans
      (div_le_div_of_nonneg_left ((abs_nonneg _).trans he) (pow_pos hp _)
        (pow_le_pow_left₀ hp.le hs _))

private theorem cutoff_slope_moment_eq (z : ℝ) :
    let B := gaussianK131InversePoly
    let d : ℝ := 19 / 16
    let D := Polynomial.C d * B - B.derivative
    D.eval z = (k131MomentPoly signedRemainderPoly d 0).eval z := by
  intro B d D
  have hB : B.natDegree < 20 := forward_inverse_degree
  have hD : D.natDegree < 20 :=
    ((Polynomial.natDegree_sub_le _ _).trans
          (max_le (Polynomial.natDegree_C_mul_le _ _)
            ((Polynomial.natDegree_derivative_le B).trans (Nat.sub_le _ _)))).trans_lt
      hB
  rw [real_anti_poly,
    show signedRemainderPoly = Polynomial.C d * D - D.derivative from
      (signed_remainder_real d B).symm,
    anti_difference_eval]
  have h := moment_poly_deriv hD (by norm_num only : (19 / 16 : ℝ) ≠ 0) z
  change (k131AntiPoly D d).derivative.eval z - d * (k131AntiPoly D d).eval z = -D.eval z at h
  linarith only [h]

/-- The deterministic and nontrivial-zero lower-endpoint costs fit the
manuscript's 17/10 remainder, with the logarithmic term retained separately. -/
theorem k131_cutoff_remainder_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 ≤ y) :
    let z := 9 / 4 + 2 * Real.log y
    let p :=
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ))
    let M := (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z
    (-(3 * p * (Real.log (2 * Real.pi) * gaussianK131InversePoly.eval z + 17 / 10 * M))) ≤
      k131PrincipalCutoff y - (231 / 5000 : ℝ) * k131LowerMass y := by
  intro z p M
  have hy0 := zero_lt_one.trans_le hy
  have hz : 0 ≤ z := by
    unfold z
    linarith only [Real.log_nonneg hy]
  have ha := cutoff_signed_moment_le (s := 35 / 16) (by norm_num only) hz
  have hb := cutoff_signed_moment_le (s := 19 / 16) le_rfl hz
  have he := cutoff_slope_moment_eq z
  dsimp only at he
  rw [← he] at hb
  have hM : 0 ≤ M := (abs_nonneg _).trans ha
  let C := AnalyticNumberTheory.RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re
  let D := Polynomial.C (19 / 16 : ℝ) * gaussianK131InversePoly - gaussianK131InversePoly.derivative
  have hd : -(16 / 25 : ℝ) * M ≤ C * D.eval z := by
    have h :=
      mul_le_mul (cutoff_zeta_constant_abs hRH) hb (abs_nonneg _)
        (by norm_num only : (0 : ℝ) ≤ 16 / 25)
    rw [← abs_mul] at h
    have hl := neg_abs_le (C * D.eval z)
    dsimp only [C, D] at hl ⊢
    linarith only [h, hl]
  have hp : 0 ≤ p := by
    have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := by
      rw [k131_amplitude_eq]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.rpow_nonneg hy0.le _)
  have hmain :
    -(Real.log (2 * Real.pi) * gaussianK131InversePoly.eval z + (17 / 10 : ℝ) * M) ≤
      -(k131MomentPoly signedRemainderPoly (35 / 16) 0).eval z -
            Real.log (2 * Real.pi) * gaussianK131InversePoly.eval z +
          C * D.eval z -
        (231 / 5000 : ℝ) * M := by
    change |(k131MomentPoly signedRemainderPoly (35 / 16) 0).eval z| ≤ M at ha
    linarith only [(abs_le.mp ha).2, hd, hM]
  have h := mul_le_mul_of_nonneg_left hmain (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3) hp)
  have hcut := k131_principal_cutoff_eq hy0
  dsimp only at hcut
  have hcut' :
    k131PrincipalCutoff y =
      3 * p *
        (-(k131MomentPoly signedRemainderPoly (35 / 16) 0).eval z -
            Real.log (2 * Real.pi) * gaussianK131InversePoly.eval z +
          C * D.eval z) := by
    rw [hcut]
    dsimp only [p, z, C, D, signedRemainderPoly]
    ring
  rw [hcut',
    show k131LowerMass y = 3 * p * M by
      unfold k131LowerMass; ring]
  linarith only [h]

/-- Under RH the principal combination has the certified spectral cost
and both explicit zero remainders, leaving only the deterministic cutoff terms. -/
theorem k131_principal_budget_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 < y) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let w := fun n : ℕ ↦ f n * ArithmeticFunction.vonMangoldt n
    let c := Real.log (2 * Real.pi)
    let B :=
      3 * ((5 / 12 : ℝ) / (2 - 19 / 16)) *
          ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
          y ^ (-(27 / 8 : ℝ)) *
          k131RemainderPoly.eval z +
        gaussianK131EdgeLoss / y ^ 5
    k131PrincipalDelta * y + 4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x + c) +
          k131PrincipalCutoff y -
        (25329 / 1000000 + (231 / 5000 : ℝ) * k131LowerMass y) -
        B ≤
      4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) := by
  intro x u z f w c B
  have hx : 1 < y ^ 2 := by
    simpa only [one_pow] using
      pow_lt_pow_left₀ hy (show (0 : ℝ) ≤ 1 from zero_le_one) (by decide : (2 : ℕ) ≠ 0)
  have h := k131_principal_explicit_lower (zero_lt_one.trans hy) hx
  have hs := (abs_le.mp (k131_principal_spectral_le hRH hy)).1
  dsimp only [x, u, z, f, w, c, B, k131PrincipalCutoff]
  dsimp only at h
  linarith only [h, hs]

/-- The principal remainder from both integration ranges and the cutoff. -/
noncomputable def k131PrincipalRem (y : ℝ) : ℝ :=
  let z := 9 / 4 + 2 * Real.log y
  let p := ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ))
  3 * p *
      ((17 / 10 : ℝ) * (k131MomentPoly k131RemainderPoly (19 / 16) 0).eval z +
        ((5 / 12 : ℝ) / (2 - 19 / 16)) * k131RemainderPoly.eval z) +
    gaussianK131EdgeLoss / y ^ 5

/-- Formula (4.2) gives a principal lower bound with the certified
spectral constant, the manuscript remainder, and the two logarithmic terms. -/
theorem k131_principal_formula_lower (hRH : RiemannHypothesis) {y : ℝ} (hy : 1 < y) :
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let p :=
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ))
    let c := Real.log (2 * Real.pi)
    let w := fun n : ℕ ↦ k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n
    k131PrincipalDelta * y + 4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi x - x + c) -
        3 * c * p * gaussianK131InversePoly.eval z -
        25329 / 1000000 -
        k131PrincipalRem y ≤
      4 * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, w n) - (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, w n) := by
  intro x u z p c w
  have h := k131_principal_budget_lower hRH hy
  have hc := k131_cutoff_remainder_lower hRH hy.le
  dsimp only at h hc
  dsimp only [x, u, z, p, c, w, k131PrincipalRem]
  linarith only [h, hc]

/-- The raw K131 Euler lower bound including the square gain. The full
unweighted sum here is the principal combination used in formula (4.2). -/
theorem k131_raw_euler_lower {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p q r : ℕ}
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let x := ⌊y ^ 2⌋₊
    let u := ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    let w := fun n : ℕ ↦ k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n
    (4 * (∑ n ∈ Finset.Icc 0 x, w n) - (∑ n ∈ Finset.Icc 0 u, w n) + 4 * (∑ n ∈ U, w n)) ≤
      ∑ n ∈ Finset.Icc 0 u, ((a n).re + (b n).re + (c n).re) * w n := by
  intro y x u U w
  have hxu : x ≤ u :=
    Nat.floor_mono (le_mul_of_one_le_right (sq_nonneg y) (Real.one_le_exp (by norm_num only)))
  have hpre :
    (∑ n ∈ Finset.Icc 0 x, ((a n).re + (b n).re + (c n).re) * w n) =
      ∑ n ∈ Finset.Icc 0 x, 3 * w n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
    · simp only [w, hΛ, mul_zero]
    have hn' := (Nat.le_floor_iff (sq_nonneg y)).mp (Finset.mem_Icc.mp hn).2
    rw [prefix_char_one a hn' hΛ ha, prefix_char_one b hn' hΛ hb, prefix_char_one c hn' hΛ hc,
      Complex.one_re]
    norm_num only
  rw [sum_prefix_tail hxu w, sum_prefix_tail hxu, hpre, ← Finset.mul_sum]
  exact
    (by
      have h := k131_forward_trace_lower hL a b c ht ha hb hc
      dsimp only [y, x, u, U, w] at h ⊢
      linarith only [h])

/-- The recovered square mass in the raw Euler bound dominates the
scalar recovery term in the K131 gap. -/
theorem k131_raw_square_lower {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
        (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y ≤
      4 * ∑ n ∈ U, k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n := by
  intro y U
  rw [Finset.mul_sum,
    Finset.sum_image
      (fun a _ b _ h ↦
        (pow_left_inj₀ (Nat.zero_le a) (Nat.zero_le b) (by decide : (2 : ℕ) ≠ 0)).mp h)]
  refine (k131_square_recovery_lower hL).trans (le_of_eq (Finset.sum_congr rfl ?_))
  intro k hk
  have hk₀ : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hk).1)
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide), Nat.cast_pow,
    recovery_weight_at_square hk₀]
  ring

private theorem principal_pos_boundary_lower (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    k131PrincipalError gaussianK131RhCoeff y ≤
      4 * (gaussianK131UnitWeight / y) * (Chebyshev.psi (y ^ 2) - y ^ 2) := by
  intro y
  have hy : 0 < y := affine_radius_pos hL
  have hx : (101 : ℝ) ≤ y ^ 2 :=
    (by norm_num only : (101 : ℝ) ≤ 1000000).trans (k131_principal_arg_gt_million hL).le
  have h := AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH hx
  rw [Real.sqrt_sq hy.le, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  let N := (2 * Real.log y) * (2 * Real.log y - Real.log (2 * Real.log y))
  change |Chebyshev.psi (y ^ 2) - y ^ 2| / y ≤ N / (8 * Real.pi) at h
  have hN : 0 ≤ N := by
    have hw := (div_nonneg (abs_nonneg _) hy.le).trans h
    simpa only [zero_mul] using (le_div_iff₀ (mul_pos (by norm_num only) Real.pi_pos)).mp hw
  have hp : (314159 / 100000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hb :=
    h.trans
      (div_le_div_of_nonneg_left hN (by norm_num only)
        (mul_le_mul_of_nonneg_left hp (by norm_num only)))
  have hlow : -(N / (8 * (314159 / 100000 : ℝ))) ≤ (Chebyshev.psi (y ^ 2) - y ^ 2) / y := by
    have h₁ := div_le_div_of_nonneg_right (neg_abs_le (Chebyshev.psi (y ^ 2) - y ^ 2)) hy.le
    rw [neg_div] at h₁
    exact (neg_le_neg hb).trans h₁
  have hm :=
    mul_le_mul_of_nonneg_left hlow (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) unit_weight_nonneg)
  unfold k131PrincipalError gaussianK131RhCoeff
  change -(gaussianK131UnitWeight / (2 * (314159 / 100000))) * N ≤ _
  refine (le_of_eq ?_).trans (hm.trans_eq ?_)
  · ring
  · ring

/-- Under RH, the K131 character trace is bounded below by the principal
comparison and the recovered square gain, using the scalar boundary cost. -/
theorem k131_euler_formula_lower (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let u := y ^ 2 * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let p₀ :=
      ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) * y ^ (-(27 / 8 : ℝ))
    let c₀ := Real.log (2 * Real.pi)
    k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
            4 * (gaussianK131UnitWeight / y) * c₀ -
          3 * c₀ * p₀ * gaussianK131InversePoly.eval z -
          25329 / 1000000 -
          k131PrincipalRem y +
        (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
          (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) ≤
      ∑ n ∈ Finset.Icc 0 ⌊u⌋₊,
        ((a n).re + (b n).re + (c n).re) *
          (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) := by
  intro y u z p₀ c₀
  have hy : 1 < y :=
    (by norm_num only : (1 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have h₁ := k131_principal_formula_lower hRH hy
  have h₂ := principal_pos_boundary_lower hRH hL
  have h₃ := k131_raw_euler_lower hL a b c ht ha hb hc
  have h₄ := k131_raw_square_lower hL
  dsimp only [y, u, z, p₀, c₀] at *
  linarith only [h₁, h₂, h₃, h₄]

/-- The raw forward deficit, the centered boundary, and the recovered square
mass together fit below four times the full RH tail envelope. -/
theorem k131_centered_deficit_upper (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let x := y ^ 2
    let u := x * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊,
          (3 - ((a n).re + (b n).re + (c n).re)) * (f n * ArithmeticFunction.vonMangoldt n)) +
        4 * ((gaussianK131UnitWeight / y) * (Chebyshev.psi x - x)) +
        4 * (∑ n ∈ U, f n * ArithmeticFunction.vonMangoldt n) ≤
      4 *
        ((gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) * gaussianK131Moment (35 / 16) +
          ∫ t in x..u,
            -deriv f t *
              (Real.log t * (Real.log t - Real.log (Real.log t)) / (8 * Real.pi) *
                Real.sqrt t)) := by
  intro y x u f U
  have hd := k131_forward_deficit_le hL a b c ht ha hb hc
  have hp :=
    mul_le_mul_of_nonneg_left (k131_centered_prime_upper hRH hL) (by norm_num only : (0 : ℝ) ≤ 4)
  have hite (n : ℕ) :
    (if n.Prime then 4 * (f n * ArithmeticFunction.vonMangoldt n) else 0) =
      4 * (if n.Prime then f n * ArithmeticFunction.vonMangoldt n else 0) := by
    rw [mul_ite, mul_zero]
  change
    (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊, _) ≤
      ∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊u⌋₊,
        if n.Prime then 4 * (f n * ArithmeticFunction.vonMangoldt n) else 0 at hd
  simp only [hite, ← Finset.mul_sum] at hd
  dsimp only [U, f, u, x, y] at hd ⊢
  linarith only [hd, hp]

/-- The forward deficit less the normalized principal boundary and
recovered squares is bounded by the prime tail less both scalar gains. -/
theorem k131_forward_budget (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    {p q r : ℕ} [NeZero p] (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ r) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (ha : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1) :
    let y := gaussianBridgeScale L
    let S := Finset.Ioc ⌊y ^ 2⌋₊ ⌊y ^ 2 * Real.exp (9 / 4)⌋₊
    let U := (Finset.Ioc ⌊y⌋₊ ⌊y * Real.exp (9 / 8)⌋₊).image (fun k : ℕ ↦ k ^ 2)
    (∑ n ∈ S,
          (3 - ((a n).re + (b n).re + (c n).re)) *
            (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n)) -
        (-4 * gaussianK131UnitWeight * ((Chebyshev.psi (y ^ 2) - y ^ 2) / y) +
          ∑ n ∈ U, 4 * k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n * (a n).re) ≤
      (∑ n ∈ S,
          if n.Prime then 4 * (k131ForwardWeight y n * ArithmeticFunction.vonMangoldt n) else 0) -
        (k131PrincipalError gaussianK131RhCoeff y +
          (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
            (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y)) := by
  exact
    sub_le_sub (k131_forward_deficit_le hL a b c ht ha hb hc)
      (k131_boundary_square_lower hRH hL a ha)

end PseudoPrime.PrimeTestBounds.MillerRabin
