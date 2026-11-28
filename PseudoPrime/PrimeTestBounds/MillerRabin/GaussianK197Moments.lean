/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogPowerTailIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectionBox
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Main integrals of the K197 reflection moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Dilation to the unit cutoff evaluates each shifted logarithmic moment. -/
private theorem log_power_shifted_tail_integral {d x : ℝ} (hd : 0 < d) (hx : 0 < x) (j : ℕ) :
    (∫ t in Set.Ioi x, (Real.log t - Real.log x) ^ j * t ^ (-d - 1)) =
      x ^ (-d) * Analysis.logPowerTailPoly d j 0 := by
  let f := fun t : ℝ ↦ (Real.log t - Real.log x) ^ j * t ^ (-d - 1)
  have h := MeasureTheory.integral_comp_mul_left_Ioi' f 1 hx
  simp only [mul_one, smul_eq_mul] at h
  have hg :
    (∫ t in Set.Ioi (1 : ℝ), f (x * t)) =
      x ^ (-d - 1) * (∫ t in Set.Ioi (1 : ℝ), Real.log t ^ j * t ^ (-d - 1)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht₀ := zero_lt_one.trans (show (1 : ℝ) < t from ht)
    dsimp only [f]
    rw [Real.log_mul hx.ne' ht₀.ne', add_sub_cancel_left, Real.mul_rpow hx.le ht₀.le]
    ring
  rw [hg, Analysis.log_power_tail_integral hd le_rfl, Real.log_one, Real.one_rpow, one_mul,
    Real.rpow_sub hx, Real.rpow_one] at h
  change (∫ t in Set.Ioi x, f t) = _
  rw [div_eq_mul_inv, mul_right_comm] at h
  rw [mul_left_comm x, mul_inv_cancel₀ hx.ne', mul_one] at h
  exact h.symm

/-- Evaluate the main integral for a relative logarithmic moment at a
positive cutoff, using the decay exponent of the K197 reflected density. -/
theorem gaussian_moment_main_197 {x : ℝ} (hx : 0 < x) (j : Fin 6) :
    (∫ t in Set.Ioi x, (Real.log t - Real.log x) ^ (j : ℕ) * t ^ (-(8 / 5) : ℝ)) =
      x ^ (-(3 / 5) : ℝ) * Analysis.logPowerTailPoly (3 / 5) j 0 := by
  have h := log_power_shifted_tail_integral (by norm_num only : (0 : ℝ) < 3 / 5) hx j
  norm_num only at h ⊢
  exact h

/-- The weight of one relative logarithmic moment in the reflected series. -/
@[expose]
noncomputable def gaussianMomentWeight197 (x : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (Real.log t - Real.log x) ^ j * t ^ (-(8 / 5) : ℝ)

/-- Differentiate the relative logarithmic weight at every positive argument. -/
theorem gaussian_moment_deriv_197 {x t : ℝ} (ht : 0 < t) (j : ℕ) :
    let v := Real.log t - Real.log x
    HasDerivAt (gaussianMomentWeight197 x j)
      ((j * v ^ (j - 1) - (8 / 5) * v ^ j) * t ^ (-(13 / 5) : ℝ)) t := by
  intro v
  have hlog := (Real.hasDerivAt_log ht.ne').sub_const (Real.log x)
  have h := (hlog.pow j).mul (Real.hasDerivAt_rpow_const (p := -(8 / 5 : ℝ)) (Or.inl ht.ne'))
  have ht' : t ^ (-(13 / 5) : ℝ) = t ^ (-(8 / 5) : ℝ) * t⁻¹ := by
    rw [show -(13 / 5 : ℝ) = -(8 / 5) - 1 by norm_num only, Real.rpow_sub ht, Real.rpow_one,
      div_eq_mul_inv]
  convert h using 1
  · funext u
    simp only [gaussianMomentWeight197, Pi.pow_apply, Pi.mul_apply]
  · rw [show -(8 / 5 : ℝ) - 1 = -(13 / 5) by norm_num only, ht']
    dsimp only [v, Pi.pow_apply]
    ring

/-- Bound the absolute centered Abel integrand by a log-square envelope
on the whole K197 range, using the finite square-root bound below one million. -/
theorem gaussian_moment_error_197 (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x) (ht : x ≤ t)
    (htn : 1423 ≤ t) (hl : 5 ≤ Real.log t) (j : ℕ) :
    let v := Real.log t - Real.log x
    |(Chebyshev.psi t - t) * deriv (gaussianMomentWeight197 x j) t| ≤
      (Real.log t ^ 2 / 24) * (j * v ^ (j - 1) + (8 / 5) * v ^ j) * t ^ (-(21 / 10) : ℝ) := by
  intro v
  have hp : 0 < t := zero_lt_one.trans_le (hx.trans ht)
  have hv : 0 ≤ v := sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) ht)
  have hlog : (4 / 5 : ℝ) ≤ Real.log t ^ 2 / 24 := by
    linarith only [pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 5) hl 2]
  have hψ : |Chebyshev.psi t - t| ≤ Real.sqrt t * (Real.log t ^ 2 / 24) := by
    by_cases h : t ≤ 1000000
    · exact
        (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million htn h).trans
          (by
            simpa only [mul_comm (4 / 5 : ℝ)] using
              mul_le_mul_of_nonneg_left hlog (Real.sqrt_nonneg t))
    · exact euler570_psi_high hRH (le_of_not_ge h)
  have hA : 0 ≤ (j : ℝ) * v ^ (j - 1) := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)
  have hB : 0 ≤ (8 / 5 : ℝ) * v ^ j := mul_nonneg (by norm_num only) (pow_nonneg hv _)
  have hab := abs_sub ((j : ℝ) * v ^ (j - 1)) ((8 / 5 : ℝ) * v ^ j)
  rw [abs_of_nonneg hA, abs_of_nonneg hB] at hab
  have hc := Real.rpow_nonneg hp.le (-(13 / 5) : ℝ)
  have he : Real.sqrt t * t ^ (-(13 / 5) : ℝ) = t ^ (-(21 / 10) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  rw [(gaussian_moment_deriv_197 hp j).deriv, abs_mul, abs_mul, abs_of_nonneg hc]
  have h :=
    mul_le_mul hψ (mul_le_mul_of_nonneg_right hab hc) (mul_nonneg (abs_nonneg _) hc)
      (mul_nonneg (Real.sqrt_nonneg t) (by positivity))
  linear_combination h + (Real.log t ^ 2 / 24) * ((j : ℝ) * v ^ (j - 1) + (8 / 5) * v ^ j) * he

/-- A shifted logarithmic power remains integrable on the tail. -/
private theorem shifted_power_integrable {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (j : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (Real.log t - Real.log x) ^ j * t ^ (-d - 1))
      (Set.Ioi x) := by
  refine (Analysis.log_power_tail_integrable hd hx j).mono' ?_ ?_
  · fun_prop
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hp := zero_lt_one.trans_le (hx.trans ht.le)
    have hv := sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) ht.le)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hv _) (Real.rpow_nonneg hp.le _))]
    exact
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hv (sub_le_self _ (Real.log_nonneg hx)) _)
        (Real.rpow_nonneg hp.le _)

/-- Integrate one power of the relative logarithm with the RH log-square
factor, retaining the three exact shifted moments. -/
theorem gaussian_moment_log_sq_integral_197 {x : ℝ} (hx : 1 ≤ x) (j : ℕ) :
    let L := Real.log x
    let P := Analysis.logPowerTailPoly (11 / 10)
    (∫ t in Set.Ioi x, Real.log t ^ 2 * (Real.log t - L) ^ j * t ^ (-(21 / 10) : ℝ)) =
      x ^ (-(11 / 10) : ℝ) * (P (j + 2) 0 + 2 * L * P (j + 1) 0 + L ^ 2 * P j 0) := by
  intro L P
  let f := fun (k : ℕ) (t : ℝ) ↦ (Real.log t - L) ^ k * t ^ (-(21 / 10) : ℝ)
  have hf (k : ℕ) : MeasureTheory.IntegrableOn (f k) (Set.Ioi x) := by
    simpa only [f, L, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only] using
      shifted_power_integrable (d := 11 / 10) (by norm_num only) hx k
  have hm (k : ℕ) : (∫ t in Set.Ioi x, f k t) = x ^ (-(11 / 10) : ℝ) * P k 0 := by
    simpa only [f, L, P, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only] using
      log_power_shifted_tail_integral (d := 11 / 10) (by norm_num only) (zero_lt_one.trans_le hx) k
  have he (t : ℝ) :
    Real.log t ^ 2 * (Real.log t - L) ^ j * t ^ (-(21 / 10) : ℝ) =
      f (j + 2) t + 2 * L * f (j + 1) t + L ^ 2 * f j t := by
    simp only [f, pow_add, pow_one]
    ring
  simp only [he]
  change (∫ t in Set.Ioi x, (f (j + 2) + (fun t ↦ (2 * L) * f (j + 1) t)) t + L ^ 2 * f j t) = _
  rw [MeasureTheory.integral_add ((hf (j + 2)).add ((hf (j + 1)).const_mul (2 * L)))
      ((hf j).const_mul (L ^ 2))]
  change (∫ t in Set.Ioi x, f (j + 2) t + (2 * L) * f (j + 1) t) + _ = _
  rw [MeasureTheory.integral_add (hf (j + 2)) ((hf (j + 1)).const_mul (2 * L))]
  simp only [MeasureTheory.integral_const_mul, hm]
  ring

private theorem shifted_log_sq_integrable {x : ℝ} (hx : 1 ≤ x) (j : ℕ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ Real.log t ^ 2 * (Real.log t - Real.log x) ^ j * t ^ (-(21 / 10) : ℝ))
      (Set.Ioi x) := by
  have h := Analysis.log_power_tail_integrable (r := 11 / 10) (by norm_num only) hx (2 + j)
  refine h.mono' (by fun_prop) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have hp := zero_lt_one.trans_le (hx.trans ht.le)
  have hv := sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) ht.le)
  simp only [Real.norm_eq_abs,
    abs_of_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hv _)) (Real.rpow_nonneg hp.le _)),
    pow_add, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv (sub_le_self _ (Real.log_nonneg hx)) j)
        (sq_nonneg _))
      (Real.rpow_nonneg hp.le _)

/-- The absolute centered error integral is bounded by the sum of
two evaluated log-square moments. -/
theorem gaussian_moment_error_integral_197 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 5 ≤ Real.log x) (j : ℕ) :
    let L := Real.log x
    let P := Analysis.logPowerTailPoly (11 / 10)
    let H := fun k ↦ x ^ (-(11 / 10) : ℝ) * (P (k + 2) 0 + 2 * L * P (k + 1) 0 + L ^ 2 * P k 0)
    MeasureTheory.IntegrableOn
        (fun t ↦ (Chebyshev.psi t - t) * deriv (gaussianMomentWeight197 x j) t) (Set.Ioi x) ∧
      |∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv (gaussianMomentWeight197 x j) t| ≤
        ((j : ℝ) * H (j - 1) + (8 / 5) * H j) / 24 := by
  intro L P H
  have hx₁ : 1 ≤ x := by linarith only [hx]
  let f := fun (k : ℕ) (t : ℝ) ↦ Real.log t ^ 2 * (Real.log t - L) ^ k * t ^ (-(21 / 10) : ℝ)
  have hf (k : ℕ) : MeasureTheory.IntegrableOn (f k) (Set.Ioi x) := shifted_log_sq_integrable hx₁ k
  have he (t : ℝ) :
    Real.log t ^ 2 / 24 * (j * (Real.log t - L) ^ (j - 1) + (8 / 5) * (Real.log t - L) ^ j) *
        t ^ (-(21 / 10) : ℝ) =
      (1 / 24) * (j * f (j - 1) t + (8 / 5) * f j t) := by
    dsimp only [f]
    ring
  have hi :=
    (((hf (j - 1)).const_mul (j : ℝ)).add ((hf j).const_mul (8 / 5 : ℝ))).const_mul (1 / 24 : ℝ)
  have hpoint :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi x)),
      ‖(Chebyshev.psi t - t) * deriv (gaussianMomentWeight197 x j) t‖ ≤
        (1 / 24) * (j * f (j - 1) t + (8 / 5) * f j t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hlog := hl.trans (Real.log_le_log (zero_lt_one.trans_le hx₁) ht.le)
    rw [Real.norm_eq_abs]
    exact (gaussian_moment_error_197 hRH hx₁ ht.le (hx.trans ht.le) hlog j).trans_eq (he t)
  refine
    ⟨hi.mono'
        (((Chebyshev.psi_mono.measurable.sub measurable_id).mul
            (measurable_deriv _)).aestronglyMeasurable)
        hpoint,
      ?_⟩
  have h := MeasureTheory.norm_integral_le_of_norm_le hi hpoint
  simp only [Real.norm_eq_abs, MeasureTheory.integral_const_mul, Pi.add_apply] at h
  rw [MeasureTheory.integral_add ((hf (j - 1)).const_mul (j : ℝ))
      ((hf j).const_mul (8 / 5 : ℝ))] at h
  have hm (k : ℕ) : (∫ t in Set.Ioi x, f k t) = H k := gaussian_moment_log_sq_integral_197 hx₁ k
  simp only [MeasureTheory.integral_const_mul, hm] at h
  linarith only [h]

private theorem shifted_mangoldt_summable (x : ℝ) (j : ℕ) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * gaussianMomentWeight197 x j n) := by
  let c := fun k : ℕ ↦ (Nat.choose j k : ℝ) * (-Real.log x) ^ (j - k)
  have h :=
    summable_sum (s := Finset.range (j + 1))
      (fun k _ ↦
        (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
              (by norm_num only) k).mul_left
          (c k))
  apply h.congr
  intro n
  simp only [gaussianMomentWeight197, sub_eq_add_neg, add_pow, c, Real.rpow_neg (Nat.cast_nonneg n),
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem shifted_boundary_zero {x : ℝ} (hx : 1 ≤ x) (j : ℕ) :
    Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * gaussianMomentWeight197 x j t) Filter.atTop
      (nhds 0) := by
  let E := fun t : ℝ ↦ (Chebyshev.psi t - t) / 4
  have hE : ∀ᶠ t : ℝ in Filter.atTop, ‖E t‖ ≤ 2 * t := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
    have h₀ := zero_le_one.trans ht
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hψ :=
      (Chebyshev.psi_le_const_mul_self h₀).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) h₀)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    exact ⟨by linarith only [Chebyshev.psi_nonneg (x := t), h₀], by linarith only [hψ, h₀]⟩
  have h :=
    ((AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 8 / 5)
            j E hE).const_mul
        (4 : ℝ)).norm
  simp only [mul_zero, norm_zero] at h
  apply squeeze_zero_norm' ?_ h
  filter_upwards [Filter.eventually_ge_atTop x] with t ht
  have ht₀ := zero_le_one.trans (hx.trans ht)
  have hv := sub_nonneg.mpr (Real.log_le_log (zero_lt_one.trans_le hx) ht)
  have hp := Real.rpow_nonneg ht₀ (-(8 / 5) : ℝ)
  have hpow := pow_le_pow_left₀ hv (sub_le_self _ (Real.log_nonneg hx)) j
  have he :
    4 * (AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (8 / 5) j t * E t) =
      (Chebyshev.psi t - t) * (Real.log t ^ j * t ^ (-(8 / 5) : ℝ)) := by
    dsimp only [E, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    ring
  rw [he, norm_mul, norm_mul,
    Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Real.log_nonneg (hx.trans ht)) _) hp)]
  unfold gaussianMomentWeight197
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg hv _) hp)]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hp) (norm_nonneg _)

/-- Centered Abel summation for any of the K197 reflection moments. -/
theorem gaussian_moment_abel_197 (hRH : RiemannHypothesis) {x : ℝ} (hx : 1423 ≤ x)
    (hl : 5 ≤ Real.log x) (j : Fin 6) :
    let f := gaussianMomentWeight197 x j
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * f n =
      x ^ (-(3 / 5) : ℝ) * Analysis.logPowerTailPoly (3 / 5) j 0 - (Chebyshev.psi x - x) * f x -
        ∫ t in Set.Ioi x, (Chebyshev.psi t - t) * deriv f t := by
  intro f
  have hx₁ : 1 ≤ x := by linarith only [hx]
  have hmain : MeasureTheory.IntegrableOn f (Set.Ioi x) := by
    change
      MeasureTheory.IntegrableOn
        (fun t : ℝ ↦ (Real.log t - Real.log x) ^ (j : ℕ) * t ^ (-(8 / 5) : ℝ)) (Set.Ioi x)
    simpa only [show -(3 / 5 : ℝ) - 1 = -(8 / 5) by norm_num only] using
      shifted_power_integrable (d := 3 / 5) (by norm_num only) hx₁ j
  have hd (t : ℝ) (ht : x ≤ t) :=
    gaussian_moment_deriv_197 (x := x) (zero_lt_one.trans_le (hx₁.trans ht)) j
  have hc (b : ℝ) : MeasureTheory.IntegrableOn (deriv f) (Set.Icc x b) := by
    refine ContinuousOn.integrableOn_Icc (ContinuousOn.congr ?_ fun t ht ↦ (hd t ht.1).deriv)
    intro t ht
    have hp := (zero_lt_one.trans_le (hx₁.trans ht.1)).ne'
    have hlog := Real.continuousAt_log hp
    have hpow := Real.continuousAt_rpow_const t (-(13 / 5) : ℝ) (Or.inl hp)
    exact
      (show
          ContinuousAt
            (fun u ↦
              ((j : ℝ) * (Real.log u - Real.log x) ^ ((j : ℕ) - 1) -
                  (8 / 5) * (Real.log u - Real.log x) ^ (j : ℕ)) *
                u ^ (-(13 / 5) : ℝ))
            t
          by fun_prop).continuousWithinAt
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral (zero_le_one.trans hx₁)
      (fun _ _ t ht ↦ (hd t ht.1).differentiableAt) (fun b _ ↦ hc b) hmain
      (gaussian_moment_error_integral_197 hRH hx hl j).1 (shifted_boundary_zero hx₁ j)
      (shifted_mangoldt_summable x j)
  rw [show (∫ t in Set.Ioi x, f t) = _ from
      gaussian_moment_main_197 (zero_lt_one.trans_le hx₁) j] at h
  exact h

private theorem moment_tail_eq (r : ℝ) (j : Fin 6) :
    let f := gaussianMomentWeight197 (r ^ 2) j
    gaussianMoment197 r j =
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * f n := by
  classical
  intro f
  let g := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n
  have hs := (shifted_mangoldt_summable (r ^ 2) j).sum_add_tsum_compl (s := Finset.Ioc 0 ⌊r ^ 2⌋₊)
  change
    (∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, g n) + (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊ }, g n.val) =
      ∑' n, g n at hs
  have hc := tsum_subtype {n : ℕ | n ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊} g
  change (∑' n : { n : ℕ // n ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊ }, g n.val) = _ at hc
  rw [hc] at hs
  have he :
    (∑' n : ℕ, {n : ℕ | n ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊}.indicator g n) = gaussianMoment197 r j := by
    unfold gaussianMoment197
    apply tsum_congr
    intro n
    by_cases hzero : n = 0
    · subst n
      simp only [Set.indicator, g, ArithmeticFunction.map_zero, zero_mul, zero_div, ite_self]
    have hN : n ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊ ↔ r ^ 2 < (n : ℝ) := by
      simp only [Finset.mem_Ioc, Nat.pos_of_ne_zero hzero, true_and, not_le,
        Nat.floor_lt (sq_nonneg r)]
    by_cases hn : r ^ 2 < (n : ℝ)
    · have hmem : n ∈ {k : ℕ | k ∉ Finset.Ioc 0 ⌊r ^ 2⌋₊} := hN.mpr hn
      rw [Set.indicator_of_mem hmem, ite_eq_left hn]
      dsimp only [g, f, gaussianMomentWeight197]
      rw [Real.log_pow, Real.rpow_neg (Nat.cast_nonneg n)]
      ring
    · rw [Set.indicator_of_notMem (fun h ↦ hn (hN.mp h)), ite_eq_right hn]
  rw [he] at hs
  linarith only [hs]

/-- Main integral plus the signed cutoff correction and the explicit
RH error allowance for one K197 logarithmic moment. -/
@[expose]
noncomputable def gaussianMomentUpper197 (r : ℝ) (j : Fin 6) : ℝ :=
  let x := r ^ 2
  let L := Real.log x
  let P := Analysis.logPowerTailPoly (11 / 10)
  let H := fun k ↦ x ^ (-(11 / 10) : ℝ) * (P (k + 2) 0 + 2 * L * P (k + 1) 0 + L ^ 2 * P k 0)
  x ^ (-(3 / 5) : ℝ) * Analysis.logPowerTailPoly (3 / 5) j 0 -
      (Chebyshev.psi x - x) * gaussianMomentWeight197 x j x +
    ((j : ℝ) * H ((j : ℕ) - 1) + (8 / 5) * H j) / 24

/-- The K197 reflection moment is bounded by its main integral, the exact
signed boundary at the cutoff, and the RH error integral majorant. -/
theorem gaussian_moment_upper_197 (hRH : RiemannHypothesis) {r : ℝ} (hx : 1423 ≤ r ^ 2)
    (hl : 5 ≤ Real.log (r ^ 2)) (j : Fin 6) :
    gaussianMoment197 r j ≤ gaussianMomentUpper197 r j := by
  have ha := gaussian_moment_abel_197 hRH hx hl j
  have hm := moment_tail_eq r j
  have he := (gaussian_moment_error_integral_197 hRH hx hl j).2
  dsimp only [gaussianMomentUpper197] at ha hm he ⊢
  linarith only [ha, hm, (abs_le.mp he).1]

/-- Under RH, combine the evaluated moment upper bounds with a certified
log-radius interval to bound the six K197 reflected shifts together. -/
theorem gaussian_joint_rh_lower_197 (hRH : RiemannHypothesis) {l u : ℚ} {r : ℝ} (hr : 1 ≤ r)
    (hx : 1423 ≤ r ^ 2) (hl : 5 ≤ Real.log (r ^ 2)) (hl₀ : 0 ≤ l)
    (hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    -4 * ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ)) *
        (∑ j : Fin 6, (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) * gaussianMomentUpper197 r j) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  exact
    gaussian_joint_moment_lower_197 hr hl₀ hlog α hα hprefix _ (gaussian_moment_upper_197 hRH hx hl)

/-- The lower endpoint contributes only to the degree-zero moment. -/
theorem gaussian_moment_weight_cutoff_197 (x : ℝ) (j : Fin 6) :
    gaussianMomentWeight197 x j x = (if j = 0 then x ^ (-(8 / 5) : ℝ) else 0) := by
  unfold gaussianMomentWeight197
  rw [sub_self]
  by_cases hj : j = 0
  · subst j
    simp only [Fin.val_zero, pow_zero, one_mul, ite_true]
  · rw [ite_eq_right hj, zero_pow (fun h ↦ hj (Fin.ext h)), zero_mul]

/-- An upper envelope for one moment from bounds for the main decay,
error decay, logarithm, and signed degree-zero boundary, respectively. -/
@[expose]
noncomputable def gaussianMomentBox197 (A B L D : ℝ) (j : Fin 6) : ℝ :=
  let P := Analysis.logPowerTailPoly (11 / 10)
  let H := fun k ↦ B * (P (k + 2) 0 + 2 * L * P (k + 1) 0 + L ^ 2 * P k 0)
  A * Analysis.logPowerTailPoly (3 / 5) j 0 + (if j = 0 then D else 0) +
    ((j : ℝ) * H ((j : ℕ) - 1) + (8 / 5) * H j) / 24

/-- Replace the real powers and logarithm in the Abel upper bound by
outward endpoint bounds, while using the supplied signed boundary charge. -/
theorem gaussian_moment_box_upper_197 (hRH : RiemannHypothesis) {r A B L D : ℝ} (hx : 1423 ≤ r ^ 2)
    (hl : 5 ≤ Real.log (r ^ 2)) (hA : (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ A)
    (hB : (r ^ 2) ^ (-(11 / 10) : ℝ) ≤ B) (hL : Real.log (r ^ 2) ≤ L)
    (hD : -(Chebyshev.psi (r ^ 2) - r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) ≤ D) (j : Fin 6) :
    gaussianMoment197 r j ≤ gaussianMomentBox197 A B L D j := by
  let x := r ^ 2
  let P := Analysis.logPowerTailPoly (11 / 10)
  have hP (k : ℕ) : 0 ≤ P k 0 := Analysis.log_power_tail_poly_nonneg (by norm_num only) le_rfl k
  have h₀ : 0 ≤ Real.log x := by linarith only [hl]
  have hSq := pow_le_pow_left₀ h₀ hL 2
  have hH (k : ℕ) :
    x ^ (-(11 / 10) : ℝ) * (P (k + 2) 0 + 2 * Real.log x * P (k + 1) 0 + Real.log x ^ 2 * P k 0) ≤
      B * (P (k + 2) 0 + 2 * L * P (k + 1) 0 + L ^ 2 * P k 0) := by
    have h₁ := mul_le_mul_of_nonneg_right hL (hP (k + 1))
    have h₂ := mul_le_mul_of_nonneg_right hSq (hP k)
    have hn :=
      add_nonneg
        (add_nonneg (hP (k + 2))
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) h₀) (hP (k + 1))))
        (mul_nonneg (sq_nonneg (Real.log x)) (hP k))
    exact
      mul_le_mul hB (by linarith only [h₁, h₂]) hn
        ((Real.rpow_nonneg (sq_nonneg r) (-(11 / 10) : ℝ)).trans hB)
  have hM :=
    mul_le_mul_of_nonneg_right hA
      (Analysis.log_power_tail_poly_nonneg (r := 3 / 5) (by norm_num only) le_rfl j)
  have hE₁ := mul_le_mul_of_nonneg_left (hH ((j : ℕ) - 1)) (Nat.cast_nonneg (j : ℕ))
  have hE₂ := hH j
  dsimp only [P, x] at hE₁ hE₂
  refine (gaussian_moment_upper_197 hRH hx hl j).trans ?_
  dsimp only [gaussianMomentUpper197, gaussianMomentBox197]
  rw [gaussian_moment_weight_cutoff_197]
  by_cases hj : j = 0
  · simp only [ite_eq_left hj]
    linarith only [hM, hE₁, hE₂, hD]
  · simp only [ite_eq_right hj, mul_zero, sub_zero, add_zero]
    linarith only [hM, hE₁, hE₂]

/-- A cell's outward bounds suffice to evaluate the full K197 reflection
allowance without further arithmetic series. -/
theorem gaussian_joint_endpoint_197 (hRH : RiemannHypothesis) {l u : ℚ} {r A B L D : ℝ} (hr : 1 ≤ r)
    (hx : 1423 ≤ r ^ 2) (hl : 5 ≤ Real.log (r ^ 2)) (hl₀ : 0 ≤ l)
    (hlog : 4 * Real.log r - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (hA : (r ^ 2) ^ (-(3 / 5) : ℝ) ≤ A)
    (hB : (r ^ 2) ^ (-(11 / 10) : ℝ) ≤ B) (hL : Real.log (r ^ 2) ≤ L)
    (hD : -(Chebyshev.psi (r ^ 2) - r ^ 2) * (r ^ 2) ^ (-(8 / 5) : ℝ) ≤ D)
    (hbox :
      0 ≤ ∑ j : Fin 6, (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) * gaussianMomentBox197 A B L D j)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    -4 * ((11 / 10 : ℝ) ^ 5 / 120 * B) *
        (∑ j : Fin 6, (↑(max 0 (jointShiftUpper197 l u j)) : ℝ) * gaussianMomentBox197 A B L D j) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hp :=
    gaussian_joint_moment_lower_197 hr hl₀ hlog α hα hprefix _
      (gaussian_moment_box_upper_197 hRH hx hl hA hB hL hD)
  have hB' : r ^ (-(11 / 5) : ℝ) ≤ B := by
    rw [← Real.rpow_natCast_mul (zero_le_one.trans hr)] at hB
    norm_num only at hB ⊢
    exact hB
  have h := mul_le_mul_of_nonneg_right hB' hbox
  refine le_trans ?_ hp
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
