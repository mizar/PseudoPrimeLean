/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLimit
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import Mathlib.Tactic.Linarith

/-! # Centered Abel summation for polynomial Euler weights -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The derivative of the logarithmic polynomial weight has the opposite sign of
the polynomial `C σ * P - P.derivative` on positive arguments. -/
public theorem euler_poly_weight_deriv (P : Polynomial ℝ) (σ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun u ↦ u ^ (-σ) * P.eval (Real.log u))
      (-(t ^ (-σ - 1) * (Polynomial.C σ * P - P.derivative).eval (Real.log t))) t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl ht.ne')).mul
      ((P.hasDerivAt (Real.log t)).comp t (Real.hasDerivAt_log ht.ne'))
  refine h.congr_deriv ?_
  rw [Real.rpow_sub ht, Real.rpow_one, div_eq_mul_inv, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  simp only [Function.comp_apply]
  ring

/-- The derivative of the Euler weight is continuous on any positive closed interval. -/
private theorem euler_poly_deriv_continuous (P : Polynomial ℝ) (σ : ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun t ↦ t ^ (-σ) * P.eval (Real.log t))) (Set.Icc a b) := by
  intro t ht
  have hp := ha.trans_le ht.1
  have h :=
    (Real.continuousAt_rpow_const t (-σ - 1) (Or.inl hp.ne')).mul
      ((Polynomial.C σ * P - P.derivative).continuous.continuousAt.comp
        (Real.continuousAt_log hp.ne'))
  exact
    h.neg.continuousWithinAt.congr
      (fun v hv ↦ (euler_poly_weight_deriv P σ (ha.trans_le hv.1)).deriv)
      (euler_poly_weight_deriv P σ hp).deriv

/-- Centered Abel summation over a finite positive interval for the polynomial weight. -/
public theorem euler_poly_centered_abel (P : Polynomial ℝ) (σ : ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (Real.log t)
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * f n) - (∫ t in a..b, f t) =
      (Chebyshev.psi b - b) * f b - (Chebyshev.psi a - a) * f a -
        ∫ t in a..b, (Chebyshev.psi t - t) * deriv f t := by
  exact
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun _ ht ↦ (euler_poly_weight_deriv P σ (ha.trans_le ht.1)).differentiableAt)
      (euler_poly_deriv_continuous P σ ha).integrableOn_Icc

/-- The polynomial tail weight is integrable at a cutoff at least one when `r > 0`. -/
public theorem euler_poly_integrable (P : Polynomial ℝ) {a r : ℝ} (ha : 1 ≤ a) (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ (-r - 1) * P.eval (Real.log t)) (Set.Ioi a) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine (hP.add hQ).congr (Filter.Eventually.of_forall (fun t ↦ ?_))
    simp only [Pi.add_apply, Polynomial.eval_add, mul_add]
  | monomial k c =>
    simpa only [MeasureTheory.IntegrableOn, Polynomial.eval_monomial, mul_assoc, mul_left_comm,
      mul_comm] using (Analysis.log_power_tail_integrable hr ha k).const_mul c

/-- A negative power of `t` makes any polynomial in `log t` tend to zero. -/
public theorem euler_poly_tendsto (P : Polynomial ℝ) {r : ℝ} (hr : 0 < r) :
    Filter.Tendsto (fun t : ℝ ↦ t ^ (-r) * P.eval (Real.log t)) Filter.atTop (nhds 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add, mul_add, add_zero] using hP.add hQ
  | monomial k c =>
    simpa only [Polynomial.eval_monomial, mul_left_comm, mul_zero] using
      (Analysis.log_pow_mul_neg_rpow_tendsto hr k).const_mul c

/-- Mangoldt-weighted logarithmic polynomial tails are summable when `σ > 1`. -/
public theorem euler_poly_summable (P : Polynomial ℝ) {σ : ℝ} (hσ : 1 < σ) :
    Summable
      (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-σ) * P.eval (Real.log n))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add, mul_add, Pi.add_apply] using hP.add hQ
  | monomial k c =>
    simpa only [Polynomial.eval_monomial, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight,
      mul_assoc, mul_left_comm, mul_comm] using
      (AnalyticNumberTheory.Arithmetic.summable_mangoldt_moment hσ k).mul_left c

/-- The elementary quadratic bound controls the centered Chebyshev error above one. -/
private theorem psi_error_le_sq {t : ℝ} (ht : 1 ≤ t) : |Chebyshev.psi t - t| ≤ t ^ 2 := by
  have ht₀ := zero_le_one.trans ht
  have hp := AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht₀
  have hs : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀ (sub_nonneg.mpr ht)]
  exact abs_le.mpr ⟨by linarith only [Chebyshev.psi_nonneg t, hs], by linarith only [hp, ht₀]⟩

/-- The centered boundary term vanishes for the Euler weight when `σ > 2`. -/
private theorem euler_poly_boundary (P : Polynomial ℝ) {σ : ℝ} (hσ : 2 < σ) :
    Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * (t ^ (-σ) * P.eval (Real.log t)))
      Filter.atTop (nhds 0) := by
  have h := euler_poly_tendsto P (sub_pos.mpr hσ)
  apply squeeze_zero_norm' ?_ (by simpa only [norm_zero] using h.norm)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht₀ := zero_lt_one.trans_le ht
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  refine (mul_le_mul_of_nonneg_right (psi_error_le_sq ht) (abs_nonneg _)).trans_eq ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _),
    abs_of_nonneg (Real.rpow_nonneg ht₀.le _), ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht₀,
    neg_sub, sub_eq_add_neg]

/-- The centered Euler error is absolutely integrable on the tail when `σ > 2`. -/
private theorem euler_poly_error_integrable (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ) (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn
      (fun t ↦ (Chebyshev.psi t - t) * deriv (fun u ↦ u ^ (-σ) * P.eval (Real.log u)) t)
      (Set.Ioi a) := by
  have h := euler_poly_integrable (Polynomial.C σ * P - P.derivative) ha (sub_pos.mpr hσ)
  refine h.norm.mono' ?_ ?_
  · exact
      ((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv _)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₁ := ha.trans ht.le
    have ht₀ := zero_lt_one.trans_le ht₁
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, (euler_poly_weight_deriv P σ ht₀).deriv,
      abs_neg]
    refine (mul_le_mul_of_nonneg_right (psi_error_le_sq ht₁) (abs_nonneg _)).trans_eq ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _),
      abs_of_nonneg (Real.rpow_nonneg ht₀.le _), ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht₀]
    congr 2
    ring

/-- Centered Abel summation on the full tail. The main integral and Mangoldt series
converge for `σ > 1`; the remaining limits are the centered error and boundary. -/
private theorem euler_poly_centered_tail_aux (P : Polynomial ℝ) {σ a : ℝ} (hσ : 1 < σ) (ha : 1 ≤ a)
    (f : ℝ → ℝ) (hf : f = fun t ↦ t ^ (-σ) * P.eval (Real.log t))
    (herr : MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv f t) (Set.Ioi a))
    (hb : Filter.Tendsto (fun t : ℝ ↦ (Chebyshev.psi t - t) * f t) Filter.atTop (nhds 0)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
      (∫ t in Set.Ioi a, f t) - (Chebyshev.psi a - a) * f a -
        ∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv f t := by
  subst f
  have ha₀ := zero_lt_one.trans_le ha
  have hmain := euler_poly_integrable P ha (sub_pos.mpr hσ)
  rw [neg_sub, sub_sub_cancel_left] at hmain
  exact
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral ha₀.le
      (fun _ _ _ ht ↦ (euler_poly_weight_deriv P σ (ha₀.trans_le ht.1)).differentiableAt)
      (fun _ _ ↦ (euler_poly_deriv_continuous P σ ha₀).integrableOn_Icc) hmain herr hb
      (euler_poly_summable P hσ)

/-- The convergent Mangoldt tail splits into its main integral, lower boundary term,
and centered Chebyshev integral for a logarithmic polynomial weight with `σ > 2`. -/
public theorem euler_poly_centered_tail (P : Polynomial ℝ) {σ a : ℝ} (hσ : 2 < σ) (ha : 1 ≤ a) :
    let f := fun t : ℝ ↦ t ^ (-σ) * P.eval (Real.log t)
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * f n) =
      (∫ t in Set.Ioi a, f t) - (Chebyshev.psi a - a) * f a -
        ∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv f t := by
  exact
    euler_poly_centered_tail_aux P ((by norm_num only : (1 : ℝ) < 2).trans hσ) ha _ rfl
      (euler_poly_error_integrable P hσ ha) (euler_poly_boundary P hσ)

end PseudoPrime.PrimeTestBounds.MillerRabin
