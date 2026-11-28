/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalWeightDeriv
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearBound
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetPowerBounds
import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLimit
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Abel bounds for the signed reflected Euler sum -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem reflected_prefix_abs (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (t : ℝ) :
    |∑ m ∈ Finset.Icc 0 ⌊t⌋₊, ArithmeticFunction.vonMangoldt m * τ m| ≤ 3 * Chebyshev.psi t := by
  rw [Chebyshev.psi_eq_sum_Icc, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, mul_comm 3]
  exact mul_le_mul_of_nonneg_left (hτ m) ArithmeticFunction.vonMangoldt_nonneg

/-- The signed Mangoldt sum over the finite reflected range is bounded by
its terminal term and a majorant for the weighted derivative integral. -/
public theorem reflected_abel_finite {b : ℝ} (hb : 1 ≤ b) (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3)
    {f G : ℝ → ℝ} (hd : ∀ t ∈ Set.Icc 1 b, DifferentiableAt ℝ f t)
    (hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 1 b))
    (hG : IntervalIntegrable G MeasureTheory.volume 1 b)
    (hle : ∀ t ∈ Set.Icc 1 b, 6 * t * |deriv f t| ≤ G t) :
    |∑ n ∈ Finset.Ioc 1 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * τ n * f n| ≤
      6 * b * |f b| + ∫ t in 1..b, G t := by
  let c := fun m : ℕ ↦ ArithmeticFunction.vonMangoldt m * τ m
  let S := fun t : ℝ ↦ ∑ m ∈ Finset.Icc 0 ⌊t⌋₊, c m
  have hS (t : ℝ) (ht : 0 ≤ t) : |S t| ≤ 6 * t := by
    have hp := AnalyticNumberTheory.Arithmetic.psi_le_111 ht
    linarith only [reflected_prefix_abs τ hτ t, hp, ht]
  have hS₁ : S 1 = 0 := by
    have h := reflected_prefix_abs τ hτ 1
    rw [Chebyshev.psi_eq_zero_of_lt_two (by norm_num only : (1 : ℝ) < 2), mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  have ha := sum_mul_eq_sub_sub_integral_mul c zero_le_one hb hd hi
  rw [← intervalIntegral.integral_of_le hb] at ha
  change
    (∑ n ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊b⌋₊, f n * c n) =
      f b * S b - f 1 * S 1 - ∫ t in 1..b, deriv f t * S t at ha
  rw [Nat.floor_one] at ha
  have hI :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr
      (integrableOn_mul_sum_Icc c (m := 0) zero_le_one hi)
  have hV : |∫ t in 1..b, deriv f t * S t| ≤ ∫ t in 1..b, G t := by
    refine
      (intervalIntegral.abs_integral_le_integral_abs hb).trans
        (intervalIntegral.integral_mono_on hb hI.abs hG (fun t ht ↦ ?_))
    rw [abs_mul, mul_comm]
    exact
      (mul_le_mul_of_nonneg_right (hS t (zero_le_one.trans ht.1)) (abs_nonneg _)).trans (hle t ht)
  change |∑ n ∈ Finset.Ioc 1 ⌊b⌋₊, c n * f n| ≤ _
  simp only [mul_comm (c _), ha, hS₁, mul_zero, sub_zero]
  have hB : |f b * S b| ≤ 6 * b * |f b| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hS b (zero_le_one.trans hb)) (abs_nonneg _)
  exact (abs_sub _ _).trans (add_le_add hB hV)

/-- On a finite cutoff the H29 log-polynomial bound has an explicit
terminal term and the integral of the absolute polynomial envelope. -/
public theorem reflected_log_abel_finite {b : ℝ} (hb : 1 ≤ b) (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3)
    (P : Polynomial ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (z : ℝ) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (z + Real.log t)
    |∑ n ∈ Finset.Ioc 1 ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * τ n * f n| ≤
      6 * b * |f b| +
        ∫ t in 1..b,
          6 * t ^ (-σ) *
            (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|) := by
  intro f
  have hpos {t : ℝ} (ht : t ∈ Set.Icc 1 b) := zero_lt_one.trans_le ht.1
  refine
    reflected_abel_finite hb τ hτ
      (fun t ht ↦ (log_euler_weight_deriv P σ z (hpos ht)).differentiableAt) ?_ ?_ ?_
  · apply ContinuousOn.integrableOn_Icc
    refine ContinuousOn.congr ?_ (fun t ht ↦ (log_euler_weight_deriv P σ z (hpos ht)).deriv)
    intro t ht
    have hz : ContinuousAt (fun u ↦ z + Real.log u) t :=
      continuousAt_const.add (Real.continuousAt_log (hpos ht).ne')
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl (hpos ht).ne')).mul
          ((P.derivative.continuous.continuousAt.comp hz).sub
            (continuousAt_const.mul (P.continuous.continuousAt.comp hz)))).continuousWithinAt
  · apply (intervalIntegrable_iff_integrableOn_Icc_of_le hb).mpr
    apply ContinuousOn.integrableOn_Icc
    intro t ht
    have hz : ContinuousAt (fun u ↦ z + Real.log u) t :=
      continuousAt_const.add (Real.continuousAt_log (hpos ht).ne')
    have hpow := Real.continuousAt_rpow_const t (-σ) (Or.inl (hpos ht).ne')
    exact
      ((continuousAt_const.mul hpow).mul
          ((continuousAt_const.mul (P.continuous.continuousAt.comp hz).abs).add
            (P.derivative.continuous.continuousAt.comp hz).abs)).continuousWithinAt
  · intro t ht
    have h :=
      mul_le_mul_of_nonneg_left (log_euler_weight_abel_le P hσ z (hpos ht))
        (by norm_num only : (0 : ℝ) ≤ 3)
    linarith only [h]

/-- Pass the finite H29 estimate to the full reflected series when the
Euler sum is summable, the envelope is integrable, and the boundary tends to zero. -/
public theorem reflected_log_abel_tsum (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ) {σ : ℝ}
    (hσ : 0 ≤ σ) (z : ℝ) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (z + Real.log t)
    let G := fun t : ℝ ↦
      6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|)
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * τ n * f n) →
      MeasureTheory.IntegrableOn G (Set.Ioi 1) →
      Filter.Tendsto (fun b : ℝ ↦ 6 * b * |f b|) Filter.atTop (nhds 0) →
      |∑' n : ℕ, ArithmeticFunction.vonMangoldt n * τ n * f n| ≤ ∫ t in Set.Ioi 1, G t := by
  intro f G hs hi hb
  let F := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * τ n * f n
  have h0 : F 0 = 0 := by simp only [F, ArithmeticFunction.map_zero, zero_mul]
  have hsum := AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix F h0 hs 1
  simp only [Nat.floor_one] at hsum
  have hprefix : (∑ n ∈ Finset.Ioc 0 1, F n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    have h1 := le_antisymm (Finset.mem_Ioc.mp hn).2 (Finset.mem_Ioc.mp hn).1
    simp only [h1, F, ArithmeticFunction.vonMangoldt_apply_one, zero_mul]
  rw [hprefix, sub_zero] at hsum
  have hin := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hi tendsto_natCast_atTop_atTop
  have hlim := (hb.comp tendsto_natCast_atTop_atTop).add hin
  rw [zero_add] at hlim
  apply le_of_tendsto_of_tendsto hsum.abs hlim
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  have ht := reflected_log_abel_finite (b := (n : ℝ)) (Nat.one_le_cast.mpr hn) τ hτ P hσ z
  simpa only [F, f, G, Function.comp_apply, Nat.floor_natCast] using ht

/-- When σ exceeds one, the terminal term of the finite H29 bound
vanishes because every logarithmic power is dominated by the positive power σ-1. -/
public theorem reflected_log_boundary_tendsto (P : Polynomial ℝ) {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    Filter.Tendsto (fun b : ℝ ↦ 6 * b * |b ^ (-σ) * P.eval (z + Real.log b)|) Filter.atTop
      (nhds 0) := by
  let Q := P.comp (Polynomial.C z + Polynomial.X)
  have hQ (b : ℝ) : Q.eval (Real.log b) = P.eval (z + Real.log b) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have hf :=
    tendsto_finsetSum (Finset.range (Q.natDegree + 1))
      (fun j _ ↦
        (AnalyticNumberTheory.DirichletLFunction.tendsto_log_pow_div_rpow (sub_pos.mpr hσ)
              j).const_mul
          (Q.coeff j))
  have hm :
    Filter.Tendsto (fun b : ℝ ↦ P.eval (z + Real.log b) / b ^ (σ - 1)) Filter.atTop (nhds 0) := by
    simp only [mul_zero, Finset.sum_const_zero] at hf
    refine hf.congr (fun b ↦ ?_)
    rw [← hQ, Polynomial.eval_eq_sum_range, Finset.sum_div]
    exact Finset.sum_congr rfl (fun _ _ ↦ (mul_div_assoc _ _ _).symm)
  have h := hm.abs.const_mul 6
  rw [abs_zero, mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with b hb
  have hp := zero_lt_one.trans_le hb
  have he : b * b ^ (-σ) = (b ^ (σ - 1))⁻¹ := by
    calc
      _ = b ^ (1 + -σ) := by rw [Real.rpow_add hp, Real.rpow_one]
      _ = _ := by rw [show (1 : ℝ) + -σ = -(σ - 1) by ring, Real.rpow_neg hp.le]
  simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg hp.le _), div_eq_mul_inv]
  rw [mul_assoc 6 b, ← mul_assoc b, he, mul_comm ((b ^ (σ - 1))⁻¹)]
  rw [abs_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hp.le _))]

/-- An absolute log-polynomial times a power of exponent below minus one
is integrable on the reflected half-line. Expand the translated polynomial
and use the existing logarithmic power moments. -/
public theorem integrable_reflected_log_poly (P : Polynomial ℝ) {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ (-σ) * |P.eval (z + Real.log t)|) (Set.Ioi 1) := by
  let Q := P.comp (Polynomial.C z + Polynomial.X)
  have hQ (t : ℝ) : Q.eval (Real.log t) = P.eval (z + Real.log t) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have hi (j : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Q.coeff j * (Real.log t ^ j * t ^ (-σ)))
      (Set.Ioi 1) := by
    have h := Analysis.log_power_tail_integrable (sub_pos.mpr hσ) (a := 1) le_rfl j
    have he : -(σ - 1) - 1 = -σ := by ring
    rw [he] at h
    exact h.const_mul _
  have hsum := MeasureTheory.integrable_finsetSum (Finset.range (Q.natDegree + 1)) (fun j _ ↦ hi j)
  refine hsum.abs.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi ?_)
  intro t ht
  have ht₀ := zero_lt_one.trans ht
  change |∑ j ∈ Finset.range (Q.natDegree + 1), Q.coeff j * (Real.log t ^ j * t ^ (-σ))| = _
  simp only [← mul_assoc, ← Finset.sum_mul, ← Polynomial.eval_eq_sum_range, hQ, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg ht₀.le _)]
  rw [mul_comm]

/-- The two absolute polynomial terms in H29 are jointly integrable. -/
public theorem integrable_reflected_abel_envelope (P : Polynomial ℝ) {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦
        6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|))
      (Set.Ioi 1) := by
  have h :=
    (((integrable_reflected_log_poly P hσ z).const_mul σ).add
          (integrable_reflected_log_poly P.derivative hσ z)).const_mul
      6
  apply h.congr
  exact
    Filter.Eventually.of_forall
      (fun t ↦ by
        simp only [Pi.add_apply]
        ring)

/-- The signed reflected series is absolutely summable for σ greater than one.
The translated polynomial is a finite combination of Mangoldt log moments. -/
public theorem summable_reflected_log_poly (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ)
    {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n * τ n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n))) := by
  let Q := P.comp (Polynomial.C z + Polynomial.X)
  let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n))
  have hQ (t : ℝ) : Q.eval (Real.log t) = P.eval (z + Real.log t) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  have hs (j : ℕ) :=
    (AnalyticNumberTheory.Arithmetic.summable_mangoldt_moment hσ j).mul_left (Q.coeff j)
  have hu : Summable f := by
    refine (summable_sum (s := Finset.range (Q.natDegree + 1)) (fun j _ ↦ hs j)).congr ?_
    intro n
    simp only [f, ← hQ, Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    ring
  apply (hu.norm.mul_left 3).of_norm_bounded
  intro n
  have he :
    ArithmeticFunction.vonMangoldt n * τ n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n)) =
      τ n * f n := by
    dsimp only [f]
    ring
  rw [he, norm_mul, Real.norm_eq_abs (τ n)]
  exact mul_le_mul_of_nonneg_right (hτ n) (norm_nonneg _)

/-- The infinite H29 Abel bound holds for every polynomial at σ greater
than one, without convergence hypotheses on either side. -/
public theorem reflected_log_abel_bound (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ) {σ : ℝ}
    (hσ : 1 < σ) (z : ℝ) :
    |∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n * τ n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n))| ≤
      ∫ t in Set.Ioi (1 : ℝ),
        6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|) := by
  exact
    reflected_log_abel_tsum τ hτ P (zero_le_one.trans hσ.le) z
      (summable_reflected_log_poly τ hτ P hσ z) (integrable_reflected_abel_envelope P hσ z)
      (reflected_log_boundary_tendsto P hσ z)

/-- A bounded complex twist of the reflected polynomial series is summable
for σ greater than one, so finite sums of twists can be combined. -/
public theorem summable_reflected_complex (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 3) (P : Polynomial ℝ)
    {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    Summable
      (fun n : ℕ ↦
        c n *
          ((ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n)) : ℝ) :
            ℂ)) := by
  let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n))
  have hf : Summable f := by
    simpa only [mul_one] using
      summable_reflected_log_poly (fun _ ↦ 1) (fun _ ↦ by norm_num only [abs_one]) P hσ z
  apply (hf.norm.mul_left 3).of_norm_bounded
  intro n
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hc n) (norm_nonneg _)

/-- Bound the real part of the reflected Euler series for complex coefficients
of norm at most three, including the sum of three Dirichlet characters. -/
public theorem reflected_complex_abel_bound (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 3) (P : Polynomial ℝ)
    {σ : ℝ} (hσ : 1 < σ) (z : ℝ) :
    |(∑' n : ℕ,
            c n *
              ((ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n)) : ℝ) :
                ℂ)).re| ≤
      ∫ t in Set.Ioi (1 : ℝ),
        6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|) := by
  rw [Complex.re_tsum (summable_reflected_complex c hc P hσ z)]
  convert
    reflected_log_abel_bound (fun n ↦ (c n).re)
      (fun n ↦ (Complex.abs_re_le_norm (c n)).trans (hc n)) P hσ z using
    2
  apply tsum_congr
  intro n
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

/-- In log coordinates the H29 envelope has decay rate σ minus one.
This form allows the absolute polynomial moments to be bounded on the half-line. -/
public theorem reflected_abel_log_coordinate (P : Polynomial ℝ) (σ z : ℝ) :
    (∫ t in Set.Ioi (1 : ℝ),
        6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|)) =
      ∫ v in Set.Ioi (0 : ℝ),
        6 * Real.exp (-(σ - 1) * v) * (σ * |P.eval (z + v)| + |P.derivative.eval (z + v)|) := by
  let g := fun t : ℝ ↦
    6 * t ^ (-σ) * (σ * |P.eval (z + Real.log t)| + |P.derivative.eval (z + Real.log t)|)
  nth_rw 1 [← Real.exp_zero]
  rw [← MeasureTheory.integral_comp_exp_Ioi g]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro v _
  have he : Real.exp (-(σ - 1) * v) = Real.exp v * Real.exp (v * (-σ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [g, smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos v), Real.log_exp, he]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
