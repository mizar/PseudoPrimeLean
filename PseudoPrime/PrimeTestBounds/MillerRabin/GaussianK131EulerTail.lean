/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Zero
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Forward
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Zero
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131CoeffCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131EndpointTails
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Kernel
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Constants
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentLimit
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPsiLeeNosal
import PseudoPrime.Analysis.LogPowerTailIntegral
import PseudoPrime.Analysis.ExponentialMomentTail
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

/-! # Integrals for the K131 Euler-tail comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The common weight in the K131 Euler tail, before the Mangoldt factor. -/
@[expose]
noncomputable def k131TailWeight (t : ℝ) : ℝ :=
  t ^ (-(35 / 16 : ℝ)) * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log t)

private theorem tail_poly_weight_deriv (P : Polynomial ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t ↦ t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t))
      (t ^ (-(51 / 16 : ℝ)) * (P.derivative.eval (Real.log t) - 35 / 16 * P.eval (Real.log t)))
      t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(35 / 16 : ℝ)) (Or.inl ht.ne')).mul
      ((P.hasDerivAt (Real.log t)).comp t (Real.hasDerivAt_log ht.ne'))
  refine h.congr_deriv ?_
  rw [show -(35 / 16 : ℝ) - 1 = -(51 / 16 : ℝ) by norm_num only,
    show t ^ (-(51 / 16 : ℝ)) = t ^ (-(35 / 16 : ℝ)) * t⁻¹ by
      rw [← Real.rpow_neg_one, ← Real.rpow_add ht,
        show -(35 / 16 : ℝ) + -1 = -(51 / 16) by norm_num only]]
  simp only [Function.comp_apply]
  ring

/-- On positive arguments, the derivative of the tail weight is the
power factor times the difference of the polynomial derivative and its scaled value. -/
theorem k131_tail_weight_deriv {t : ℝ} (ht : 0 < t) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    HasDerivAt k131TailWeight
      (t ^ (-(51 / 16 : ℝ)) * (P.derivative.eval (Real.log t) - 35 / 16 * P.eval (Real.log t)))
      t := by
  exact tail_poly_weight_deriv _ ht

private theorem tail_poly_deriv_continuous (P : Polynomial ℝ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv (fun t ↦ t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t))) (Set.Icc a b) := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := tail_poly_weight_deriv P (ha.trans_le ht.1)
  intro t ht
  have hp := ha.trans_le ht.1
  have hl := Real.continuousAt_log hp.ne'
  have hr := Real.continuousAt_rpow_const t (-(51 / 16 : ℝ)) (Or.inl hp.ne')
  exact
    (hr.mul
          ((P.derivative.continuous.continuousAt.comp hl).sub
            (continuousAt_const.mul (P.continuous.continuousAt.comp hl)))).continuousWithinAt.congr
      (fun v hv ↦ (hd v hv).deriv) (hd t ht).deriv

private theorem tail_deriv_continuous {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (deriv k131TailWeight) (Set.Icc a b) :=
  tail_poly_deriv_continuous _ ha

/-- The exact centered Abel formula for the K131 tail on a finite positive interval.
It retains both lower and upper Chebyshev error terms. -/
theorem k131_tail_centered_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * k131TailWeight n) -
        (∫ t in a..b, k131TailWeight t) =
      (Chebyshev.psi b - b) * k131TailWeight b - (Chebyshev.psi a - a) * k131TailWeight a -
        ∫ t in a..b, (Chebyshev.psi t - t) * deriv k131TailWeight t := by
  exact
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun _ ht ↦ (k131_tail_weight_deriv (ha.trans_le ht.1)).differentiableAt)
      (tail_deriv_continuous ha).integrableOn_Icc

/-- In logarithmic coordinates, the main Euler-tail integral is the
difference of the two exponential moments used in the scalar comparison. -/
theorem k131_tail_main_integral (a b : ℝ) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    (∫ t in a..b, Real.exp (-(19 / 16 : ℝ) * t) * P.eval t) =
      Real.exp (-(19 / 16 : ℝ) * a) * (k131MomentPoly P (19 / 16) 0).eval a -
        Real.exp (-(19 / 16 : ℝ) * b) * (k131MomentPoly P (19 / 16) 0).eval b := by
  have hP : (gaussianK131Fourier + k131GramEulerPoly).natDegree ≤ 9 :=
    Polynomial.natDegree_add_le_of_degree_le degree_fourier
      (by simpa only [k131GramEulerPoly] using degree_gram_fourier)
  exact k131_exp_poly_integral (hP.trans_lt (by decide)) (by norm_num only : (19 / 16 : ℝ) ≠ 0) a b

/-- For positive endpoints the main integral in the centered Abel formula
is exactly the difference of the logarithmic endpoint moments. -/
theorem k131_tail_weight_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    (∫ t in a..b, k131TailWeight t) =
      Real.exp (-(19 / 16 : ℝ) * Real.log a) * (k131MomentPoly P (19 / 16) 0).eval (Real.log a) -
        Real.exp (-(19 / 16 : ℝ) * Real.log b) *
          (k131MomentPoly P (19 / 16) 0).eval (Real.log b) := by
  intro P
  let g := fun v ↦ Real.exp (-(19 / 16 : ℝ) * v) * P.eval v
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := ha.trans_le (Set.uIcc_of_le hab ▸ ht).1
  have hi := continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous
  have h :=
    intervalIntegral.integral_comp_mul_deriv' (f := Real.log) (f' := fun t ↦ t⁻¹) (g := g)
      (fun t ht ↦ Real.hasDerivAt_log (hp t ht).ne') hi hg.continuousOn
  rw [← k131_tail_main_integral (Real.log a) (Real.log b), ← h]
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' := hp t ht
  change
    t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t) =
      Real.exp (-(19 / 16 : ℝ) * Real.log t) * P.eval (Real.log t) * t⁻¹
  rw [mul_comm (-(19 / 16 : ℝ)), ← Real.rpow_def_of_pos ht', ← Real.rpow_neg_one, mul_right_comm, ←
    Real.rpow_add ht']
  congr 2
  norm_num only

private theorem exp_poly_tendsto_zero (P : Polynomial ℝ) {s : ℝ} (hs : 0 < s) :
    Filter.Tendsto (fun t : ℝ ↦ Real.exp (-s * t) * P.eval t) Filter.atTop (nhds 0) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add, mul_add, add_zero] using hP.add hQ
  | monomial n
    c =>
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) s hs).const_mul c
    simpa only [Real.rpow_natCast, Polynomial.eval_monomial, mul_zero, mul_left_comm, mul_assoc,
      mul_comm] using h

/-- The main integral of the K131 tail converges to its lower endpoint moment. -/
theorem k131_tail_main_tendsto {a : ℝ} (ha : 0 < a) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    Filter.Tendsto (fun b : ℝ ↦ ∫ t in a..b, k131TailWeight t) Filter.atTop
      (nhds
        (Real.exp (-(19 / 16 : ℝ) * Real.log a) *
          (k131MomentPoly P (19 / 16) 0).eval (Real.log a))) := by
  intro P
  have h :=
    (exp_poly_tendsto_zero (k131MomentPoly P (19 / 16) 0)
          (by norm_num only : (0 : ℝ) < 19 / 16)).comp
      Real.tendsto_log_atTop
  let C := Real.exp (-(19 / 16 : ℝ) * Real.log a) * (k131MomentPoly P (19 / 16) 0).eval (Real.log a)
  have hconst : Filter.Tendsto (fun _ : ℝ ↦ C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hlim := hconst.sub h
  rw [sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact (k131_tail_weight_integral ha hb).symm

private theorem tail_poly_boundary_tendsto (P : Polynomial ℝ) :
    Filter.Tendsto
      (fun b : ℝ ↦ (Chebyshev.psi b - b) * (b ^ (-(35 / 16 : ℝ)) * P.eval (Real.log b)))
      Filter.atTop (nhds 0) := by
  have h :=
    (exp_poly_tendsto_zero P (by norm_num only : (0 : ℝ) < 3 / 16)).comp Real.tendsto_log_atTop
  apply squeeze_zero_norm' ?_ (by simpa only [Real.norm_eq_abs, norm_zero] using h.norm)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
  have ht₀ := zero_lt_one.trans_le ht
  have hψ := AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht₀.le
  have hsq : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀.le (sub_nonneg.mpr ht)]
  have ha : |Chebyshev.psi t - t| ≤ t ^ 2 :=
    abs_le.mpr ⟨by linarith only [Chebyshev.psi_nonneg t, hsq], by linarith only [hψ, ht₀]⟩
  rw [Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ t ^ 2 * |t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t)| :=
      mul_le_mul_of_nonneg_right ha (abs_nonneg _)
    _ = |Real.exp (-(3 / 16 : ℝ) * Real.log t) * P.eval (Real.log t)| := by
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _), abs_mul,
        abs_of_nonneg (Real.exp_pos _).le, ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht₀,
        mul_comm (-(3 / 16 : ℝ)), ← Real.rpow_def_of_pos ht₀]
      norm_num only

/-- The upper Chebyshev boundary in the centered Euler-tail formula vanishes
at infinity, already under the elementary quadratic bound for Chebyshev psi. -/
theorem k131_tail_boundary_tendsto :
    Filter.Tendsto (fun b : ℝ ↦ (Chebyshev.psi b - b) * k131TailWeight b) Filter.atTop (nhds 0) :=
  tail_poly_boundary_tendsto _

private theorem tail_mangoldt_poly_summable (P : Polynomial ℝ) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(35 / 16 : ℝ)) * P.eval (Real.log n))) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add, mul_add, Pi.add_apply] using hP.add hQ
  | monomial k
    c =>
    have h :=
      AnalyticNumberTheory.Arithmetic.summable_mangoldt_moment
        (by norm_num only : (1 : ℝ) < 35 / 16) k
    simpa only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, Polynomial.eval_monomial,
      mul_left_comm, mul_assoc, mul_comm] using h.mul_left c

/-- If the centered error integral converges to `E`, the full K131 Mangoldt
tail equals the lower main moment minus the lower Chebyshev boundary and `E`. -/
theorem k131_tail_centered_tsum {a E : ℝ} (ha : 0 < a)
    (herr :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t in a..b, (Chebyshev.psi t - t) * deriv k131TailWeight t)
        Filter.atTop (nhds E)) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * k131TailWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * k131TailWeight n) =
      Real.exp (-(19 / 16 : ℝ) * Real.log a) * (k131MomentPoly P (19 / 16) 0).eval (Real.log a) -
        (Chebyshev.psi a - a) * k131TailWeight a -
        E := by
  exact
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_tsum ha.le
      (fun _ _ _ ht ↦ (k131_tail_weight_deriv (ha.trans_le ht.1)).differentiableAt)
      (fun _ _ ↦ (tail_deriv_continuous ha).integrableOn_Icc) (k131_tail_main_tendsto ha) herr
      k131_tail_boundary_tendsto (tail_mangoldt_poly_summable _)

private theorem tail_poly_integrable (P : Polynomial ℝ) {a r : ℝ} (ha : 1 ≤ a) (hr : 0 < r) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ t ^ (-r - 1) * P.eval (Real.log t)) (Set.Ioi a) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    refine (hP.add hQ).congr (Filter.Eventually.of_forall (fun t ↦ ?_))
    simp only [Pi.add_apply, Polynomial.eval_add, mul_add]
  | monomial k c =>
    have h := (Analysis.log_power_tail_integrable hr ha k).const_mul c
    simpa only [MeasureTheory.IntegrableOn, Polynomial.eval_monomial, mul_assoc, mul_left_comm,
      mul_comm] using h

/-- The centered Chebyshev error of the K131 weight is absolutely integrable
on any tail starting at or above one. -/
theorem k131_tail_error_integrable {a : ℝ} (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ (Chebyshev.psi t - t) * deriv k131TailWeight t)
      (Set.Ioi a) := by
  let P := gaussianK131Fourier + k131GramEulerPoly
  let Q := P.derivative - Polynomial.C (35 / 16 : ℝ) * P
  have hQ := tail_poly_integrable Q ha (by norm_num only : (0 : ℝ) < 3 / 16)
  rw [show -(3 / 16 : ℝ) - 1 = -(19 / 16) by norm_num only] at hQ
  refine hQ.norm.mono' ?_ ?_
  · exact
      ((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv k131TailWeight)).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht₁ : 1 ≤ t := ha.trans ht.le
    have ht₀ := zero_lt_one.trans_le ht₁
    have hψ := AnalyticNumberTheory.Arithmetic.psi_le_self_sq ht₀.le
    have hsq : t ≤ t ^ 2 := by nlinarith only [mul_nonneg ht₀.le (sub_nonneg.mpr ht₁)]
    have he : |Chebyshev.psi t - t| ≤ t ^ 2 :=
      abs_le.mpr ⟨by linarith only [Chebyshev.psi_nonneg t, hsq], by linarith only [hψ, ht₀]⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans_eq ?_
    rw [(k131_tail_weight_deriv ht₀).deriv]
    simp only [Q, P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _),
      abs_of_nonneg (Real.rpow_nonneg ht₀.le _), ← mul_assoc, ← Real.rpow_two, ← Real.rpow_add ht₀]
    norm_num only

/-- The K131 Mangoldt tail is the lower main moment with the exact lower
boundary correction and the absolutely convergent improper Chebyshev error. -/
theorem k131_tail_centered_integral {a : ℝ} (ha : 1 ≤ a) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * k131TailWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * k131TailWeight n) =
      Real.exp (-(19 / 16 : ℝ) * Real.log a) * (k131MomentPoly P (19 / 16) 0).eval (Real.log a) -
        (Chebyshev.psi a - a) * k131TailWeight a -
        ∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv k131TailWeight t := by
  exact
    k131_tail_centered_tsum (zero_lt_one.trans_le ha)
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi a (k131_tail_error_integrable ha)
        Filter.tendsto_id)

private theorem tail_psi_rh (hRH : RiemannHypothesis) {t : ℝ} (ht : 101 ≤ t) (hl : 1 ≤ Real.log t) :
    |Chebyshev.psi t - t| ≤ Real.sqrt t * Real.log t ^ 2 / 24 := by
  have ht₀ := (by norm_num only : (0 : ℝ) < 101).trans_le ht
  have hs := Real.sqrt_pos.2 ht₀
  have h := (div_le_iff₀ hs).mp (AnalyticNumberTheory.Arithmetic.psi_lee_nosal_of_RH hRH ht)
  have hπ : (24 : ℝ) ≤ 8 * Real.pi := by linarith only [Real.pi_gt_three]
  have hn :=
    mul_le_mul_of_nonneg_left (sub_le_self (Real.log t) (Real.log_nonneg hl)) (zero_le_one.trans hl)
  calc
    _ ≤ Real.log t ^ 2 / (8 * Real.pi) * Real.sqrt t :=
      h.trans
        (mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right (by simpa only [pow_two] using hn) (by positivity)) hs.le)
    _ ≤ _ := by
      rw [mul_comm, ← mul_div_assoc]
      exact div_le_div_of_nonneg_left (mul_nonneg hs.le (sq_nonneg _)) (by norm_num only) hπ

/-- Under RH, the centered Euler-tail error is bounded by the logarithmic
square times the absolute derivative polynomial, with constant `1/24`. -/
theorem k131_tail_rh_error (hRH : RiemannHypothesis) {a : ℝ} (ha : 101 ≤ a) (hl : 1 ≤ Real.log a) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let Q := Polynomial.X ^ 2 * (P.derivative - Polynomial.C (35 / 16 : ℝ) * P)
    |∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv k131TailWeight t| ≤
      ∫ t in Set.Ioi a, |t ^ (-(43 / 16 : ℝ)) * Q.eval (Real.log t)| / 24 := by
  intro P Q
  have ha₁ := (by norm_num only : (1 : ℝ) ≤ 101).trans ha
  have hQ := tail_poly_integrable Q ha₁ (by norm_num only : (0 : ℝ) < 27 / 16)
  rw [show -(27 / 16 : ℝ) - 1 = -(43 / 16) by norm_num only] at hQ
  have hi := hQ.norm.div_const 24
  simp only [Real.norm_eq_abs] at hi
  rw [← Real.norm_eq_abs]
  apply MeasureTheory.norm_integral_le_of_norm_le hi
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht₀ := zero_lt_one.trans_le (ha₁.trans ht.le)
  have hlog := hl.trans (Real.log_le_log (zero_lt_one.trans_le ha₁) ht.le)
  rw [Real.norm_eq_abs, abs_mul]
  refine
    (mul_le_mul_of_nonneg_right (tail_psi_rh hRH (ha.trans ht.le) hlog) (abs_nonneg _)).trans_eq ?_
  rw [(k131_tail_weight_deriv ht₀).deriv]
  simp only [P, Q, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C]
  simp only [abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le (-(51 / 16 : ℝ))),
    abs_of_nonneg (Real.rpow_nonneg ht₀.le (-(43 / 16 : ℝ))),
    abs_of_nonneg (sq_nonneg (Real.log t))]
  rw [Real.sqrt_eq_rpow]
  have hp : t ^ (1 / 2 : ℝ) * t ^ (-51 / 16 : ℝ) = t ^ (-43 / 16 : ℝ) := by
    rw [← Real.rpow_add ht₀]
    norm_num only
  ring_nf
  rw [← hp]
  ring

/-- Under RH, the main moment plus the derivative majorant bounds the infinite
Mangoldt tail, with the lower Chebyshev boundary retained exactly. -/
theorem k131_mangoldt_tail_rh_le (hRH : RiemannHypothesis) {a : ℝ} (ha : 101 ≤ a)
    (hl : 1 ≤ Real.log a) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let Q := Polynomial.X ^ 2 * (P.derivative - Polynomial.C (35 / 16 : ℝ) * P)
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * k131TailWeight n) -
        (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, ArithmeticFunction.vonMangoldt n * k131TailWeight n) ≤
      Real.exp (-(19 / 16 : ℝ) * Real.log a) * (k131MomentPoly P (19 / 16) 0).eval (Real.log a) -
          (Chebyshev.psi a - a) * k131TailWeight a +
        ∫ t in Set.Ioi a, |t ^ (-(43 / 16 : ℝ)) * Q.eval (Real.log t)| / 24 := by
  intro P Q
  have he := k131_tail_centered_integral ((by norm_num only : (1 : ℝ) ≤ 101).trans ha)
  have h := k131_tail_rh_error hRH ha hl
  linarith only [he, (abs_le.mp h).1]

/-- A polynomial of degree below twenty has a closed-form logarithmic
power moment on a tail starting at or above one. -/
theorem k131_tail_poly_moment {P : Polynomial ℝ} (hP : P.natDegree < 20) {a r : ℝ} (ha : 1 ≤ a)
    (hr : 0 < r) :
    (∫ t in Set.Ioi a, t ^ (-r - 1) * P.eval (Real.log t)) =
      Real.exp (-r * Real.log a) * (k131MomentPoly P r 0).eval (Real.log a) := by
  let f := fun t : ℝ ↦ t ^ (-r - 1) * P.eval (Real.log t)
  let g := fun v : ℝ ↦ Real.exp (-r * v) * P.eval v
  have ha₀ := zero_lt_one.trans_le ha
  have hfinite (b : ℝ) (hb : a ≤ b) : (∫ t in a..b, f t) = ∫ v in Real.log a..Real.log b, g v := by
    have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t := ha₀.trans_le (Set.uIcc_of_le hb ▸ ht).1
    have hg : Continuous g :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul P.continuous
    rw [←
      intervalIntegral.integral_comp_mul_deriv' (f := Real.log) (f' := fun t ↦ t⁻¹) (g := g)
        (fun t ht ↦ Real.hasDerivAt_log (hp t ht).ne')
        (continuousOn_id.inv₀ (fun t ht ↦ (hp t ht).ne')) hg.continuousOn]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only [f, g, Function.comp_apply]
    rw [mul_comm (-r), ← Real.rpow_def_of_pos (hp t ht), ← Real.rpow_neg_one, mul_right_comm, ←
      Real.rpow_add (hp t ht), sub_eq_add_neg]
  let C := Real.exp (-r * Real.log a) * (k131MomentPoly P r 0).eval (Real.log a)
  have hc : Filter.Tendsto (fun _ : ℝ ↦ C) Filter.atTop (nhds C) := tendsto_const_nhds
  have hzero := (exp_poly_tendsto_zero (k131MomentPoly P r 0) hr).comp Real.tendsto_log_atTop
  have hlim := hc.sub hzero
  rw [sub_zero] at hlim
  refine
    tendsto_nhds_unique
      (MeasureTheory.intervalIntegral_tendsto_integral_Ioi a (tail_poly_integrable P ha hr)
        Filter.tendsto_id)
      (hlim.congr' ?_)
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  change _ = ∫ t in a..b, f t
  rw [hfinite b hb, k131_exp_poly_integral hP hr.ne']
  rfl

/-- When the combined kernel is decreasing above the cutoff, the RH
error majorant is the exact moment of the nonnegative derivative polynomial. -/
theorem k131_tail_rh_error_moment (hRH : RiemannHypothesis) {a : ℝ} (ha : 101 ≤ a)
    (hl : 1 ≤ Real.log a)
    (hs :
      ∀ v : ℝ,
        Real.log a ≤ v →
          let P := gaussianK131Fourier + k131GramEulerPoly
          P.derivative.eval v ≤ (35 / 16 : ℝ) * P.eval v) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    |∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv k131TailWeight t| ≤
      Real.exp (-(27 / 16 : ℝ) * Real.log a) * (k131MomentPoly D (27 / 16) 0).eval (Real.log a) /
        24 := by
  intro P D
  have ha₁ := (by norm_num only : (1 : ℝ) ≤ 101).trans ha
  have hP : P.natDegree ≤ 9 :=
    Polynomial.natDegree_add_le_of_degree_le degree_fourier
      (by simpa only [k131GramEulerPoly] using degree_gram_fourier)
  have hD : D.natDegree < 20 := by
    have hd :=
      Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial ℝ) ^ 2) (q :=
        Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    have he :=
      degree_sub (degree_mul_C hP (35 / 16 : ℝ))
        ((Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hP))
    exact
      hd.trans_lt
        (by
          rw [Polynomial.natDegree_pow, Polynomial.natDegree_X]
          exact (Nat.add_le_add_left he _).trans_lt (by decide))
  refine (k131_tail_rh_error hRH ha hl).trans_eq ?_
  rw [← k131_tail_poly_moment hD ha₁ (by norm_num only : (0 : ℝ) < 27 / 16),
    show -(27 / 16 : ℝ) - 1 = -(43 / 16) by norm_num only, ← MeasureTheory.integral_div]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht₀ := zero_lt_one.trans_le (ha₁.trans ht.le)
  have h := hs (Real.log t) (Real.log_le_log (zero_lt_one.trans_le ha₁) ht.le)
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
    Polynomial.eval_C]
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht₀.le _),
    abs_of_nonneg (sq_nonneg (Real.log t)), abs_of_nonpos (sub_nonpos.mpr h), neg_sub]

private def tailShiftWeight (s d : ℚ) (k j : ℕ) : ℚ :=
  -(s * (14 : ℚ) ^ (j - k) * j.choose k - d * (k + 1) * (14 : ℚ) ^ (j - (k + 1)) * j.choose (k + 1))

private def tailShiftUpper (s d : ℚ) (k : ℕ) : ℚ :=
  (∑ j ∈ Finset.range 10, tailShiftWeight s d k j * fourierCoeff j) +
    gramLinearUpper (Finset.range 10) id (tailShiftWeight s d k)

private theorem tail_shift_cert (k : Fin 10) :
    tailShiftUpper 1 0 k ≤ 0 ∧ tailShiftUpper (35 / 16) 1 k ≤ 0 := by fin_cases k <;> decide +kernel

private theorem tail_shift_coeff_le (s d : ℚ) (k : ℕ) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let S := shiftPoly P 14
    (-((s : ℝ) * S.coeff k - (d : ℝ) * S.derivative.coeff k) ≤ (tailShiftUpper s d k : ℝ)) := by
  intro P S
  have hP : P.natDegree < 10 :=
    Nat.lt_succ_of_le
      (Polynomial.natDegree_add_le_of_degree_le degree_fourier
        (by simpa only [k131GramEulerPoly] using degree_gram_fourier))
  have hcoeff (j : ℕ) : P.coeff j = (fourierCoeff j : ℝ) + gramFourierCoeff j := by
    simp only [P, Polynomial.coeff_add, k131GramEulerPoly, coeff_gram_fourier, coeff_fourier]
  have he (j : ℕ) := coeff_shift_real hP hcoeff 14 j
  have h := gram_fourier_linear_le (Finset.range 10) id (tailShiftWeight s d k)
  simp only [tailShiftUpper, Rat.cast_add]
  refine le_trans ?_ (add_le_add_right h _)
  apply le_of_eq
  change -((s : ℝ) * (shiftPoly P 14).coeff k - (d : ℝ) * (shiftPoly P 14).derivative.coeff k) = _
  rw [Polynomial.coeff_derivative, he k, he (k + 1)]
  simp only [shiftedRealCoeff, Rat.cast_sum, Rat.cast_mul, ← Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [tailShiftWeight, Rat.cast_neg, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_add, Rat.cast_one, id_eq]
  ring

private theorem tail_shift_eval_nonneg (s d : ℚ) (hc : ∀ k : Fin 10, tailShiftUpper s d k ≤ 0)
    {v : ℝ} (hv : 14 ≤ v) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    0 ≤ (s : ℝ) * P.eval v - (d : ℝ) * P.derivative.eval v := by
  intro P
  let S := shiftPoly P 14
  let Q := Polynomial.C (s : ℝ) * S - Polynomial.C (d : ℝ) * S.derivative
  have hP : P.natDegree ≤ 9 :=
    Polynomial.natDegree_add_le_of_degree_le degree_fourier
      (by simpa only [k131GramEulerPoly] using degree_gram_fourier)
  have hS : S.natDegree ≤ 9 := degree_shift hP _
  have hQ : Q.natDegree ≤ 9 :=
    degree_sub (degree_mul_C hS _)
      (degree_mul_C ((Polynomial.natDegree_derivative_le S).trans ((Nat.sub_le _ _).trans hS)) _)
  have hn (k : ℕ) (hk : k ∈ Finset.range 10) : 0 ≤ Q.coeff k := by
    have hr : tailShiftUpper s d k ≤ 0 := hc ⟨k, Finset.mem_range.mp hk⟩
    have hr' : (tailShiftUpper s d k : ℝ) ≤ 0 := by exact_mod_cast hr
    have h := (tail_shift_coeff_le s d k).trans hr'
    simpa only [Q, Polynomial.coeff_sub, Polynomial.coeff_C_mul, neg_nonpos] using h
  have hval : 0 ≤ Q.eval (v - 14) := by
    conv_rhs => rw [Q.as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le hQ)]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
    exact Finset.sum_nonneg (fun k hk ↦ mul_nonneg (hn k hk) (pow_nonneg (sub_nonneg.mpr hv) _))
  have harg : v - 14 + 14 = v := sub_add_cancel v 14
  simpa only [Q, S, shiftPoly, Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, mul_one, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, one_mul, harg] using hval

/-- The combined Fourier polynomial is nonnegative and gives a decreasing
power-log weight for logarithmic arguments at least fourteen. -/
theorem k131_tail_fourier_signs {v : ℝ} (hv : 14 ≤ v) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    0 ≤ P.eval v ∧ P.derivative.eval v ≤ (35 / 16 : ℝ) * P.eval v := by
  constructor
  · simpa only [Rat.cast_one, Rat.cast_zero, one_mul, zero_mul, sub_zero] using
      tail_shift_eval_nonneg 1 0 (fun k ↦ (tail_shift_cert k).1) hv
  · have h := tail_shift_eval_nonneg (35 / 16) 1 (fun k ↦ (tail_shift_cert k).2) hv
    exact
      sub_nonneg.mp (by simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, one_mul] using h)

/-- For cutoffs with logarithm at least fourteen, the K131 RH error
is bounded by the explicit derivative moment with no additional sign hypothesis. -/
theorem k131_tail_rh_error_from14 (hRH : RiemannHypothesis) {a : ℝ} (ha : 101 ≤ a)
    (hl : 14 ≤ Real.log a) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    |∫ t in Set.Ioi a, (Chebyshev.psi t - t) * deriv k131TailWeight t| ≤
      Real.exp (-(27 / 16 : ℝ) * Real.log a) * (k131MomentPoly D (27 / 16) 0).eval (Real.log a) /
        24 := by
  exact
    k131_tail_rh_error_moment hRH ha ((by norm_num only : (1 : ℝ) ≤ 14).trans hl)
      (fun _ hv ↦ (k131_tail_fourier_signs (hl.trans hv)).2)

private theorem k131_tail_subtype_eq {f : ℕ → ℝ} (hf : Summable f) (h0 : f 0 = 0) (a : ℝ) :
    (∑' n : { n : ℕ // ⌊a⌋₊ < n }, f n.val) = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n := by
  have he := hf.sum_add_tsum_compl (s := Finset.Icc 0 ⌊a⌋₊)
  have hs : (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n) = ∑ n ∈ Finset.Icc 0 ⌊a⌋₊, f n := by
    refine
      Finset.sum_subset (fun n hn ↦ Finset.mem_Icc.mpr ⟨Nat.zero_le n, (Finset.mem_Ioc.mp hn).2⟩)
        (fun n hn hnot ↦ ?_)
    have hn₀ : n = 0 := by
      by_contra h
      exact hnot (Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h, (Finset.mem_Icc.mp hn).2⟩)
    simpa only [hn₀] using h0
  have hc : (↑(Finset.Icc 0 ⌊a⌋₊) : Set ℕ)ᶜ = {n | ⌊a⌋₊ < n} := by
    ext n
    simp only [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_Icc, Nat.zero_le, true_and, not_le,
      Set.mem_ofPred_eq]
  rw [← hs, hc] at he
  change
    (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n) + (∑' n : { n : ℕ // ⌊a⌋₊ < n }, f n.val) = ∑' n : ℕ, f n at he
  change (∑' n : { n : ℕ // ⌊a⌋₊ < n }, f n.val) = (∑' n : ℕ, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n
  linarith only [he]

/-- With RH and a lower bound of minus one for the trace, the combined
Euler tail is bounded by four times the K131 main and derivative moments,
keeping the Chebyshev error at the lower endpoint exact. -/
theorem k131_trace_tail_rh_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {X : ℝ} (hX : Real.exp 7 ≤ X) (hX₁ : 101 ≤ X) (hl : 14 ≤ Real.log X)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) ≤
      4 *
        (Real.exp (-(19 / 16 : ℝ) * Real.log X) * (k131MomentPoly P (19 / 16) 0).eval (Real.log X) -
            (Chebyshev.psi X - X) * k131TailWeight X +
          Real.exp (-(27 / 16 : ℝ) * Real.log X) *
              (k131MomentPoly D (27 / 16) 0).eval (Real.log X) /
            24) := by
  intro P D
  let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * k131TailWeight n
  have hf : Summable f := tail_mangoldt_poly_summable _
  have hm := (hf.subtype (fun n : ℕ ↦ ⌊X⌋₊ < n)).hasSum.mul_left (4 : ℝ)
  have hmax (n : { n : ℕ // ⌊X⌋₊ < n }) :
    max 0
        ((ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (35 / 16 : ℝ)) *
          P.eval (Real.log n.val)) =
      f n.val := by
    have hn := (Nat.floor_lt ((Real.exp_pos 7).le.trans hX)).mp n.property
    have hp :=
      (k131_tail_fourier_signs (hl.trans (Real.log_le_log ((Real.exp_pos 7).trans_le hX) hn.le))).1
    rw [max_eq_right
        (mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          hp)]
    simp only [f, k131TailWeight, Real.rpow_neg (Nat.cast_nonneg n.val), div_eq_mul_inv, mul_assoc]
  have ht :=
    k131_tail_le_four a b c hX htrace
      (by
        dsimp only [P] at hmax
        simpa only [hmax, Function.comp_apply] using hm)
  have he := k131_tail_centered_integral ((by norm_num only : (1 : ℝ) ≤ 101).trans hX₁)
  have h := k131_tail_rh_error_from14 hRH hX₁ hl
  change _ ≤ 4 * (∑' n : { n : ℕ // ⌊X⌋₊ < n }, f n.val) at ht
  rw [k131_tail_subtype_eq hf (by simp only [f, ArithmeticFunction.map_zero, zero_mul])] at ht
  linarith only [ht, he, (abs_le.mp h).1]

/-- On the K131 bridge, the combined trace tail is bounded by the main
moment and the sum of the RH endpoint and derivative moments. -/
theorem k131_bridge_trace_tail_le {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r)
    (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := gaussianBridgeScale L ^ 2
    let v := Real.log X
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    k131CosineTail a b c X 0 + k131GramMix (k131CosineTail a b c X) ≤
      4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6 := by
  intro X v P D
  have hY : (100 : ℝ) ≤ gaussianBridgeScale L :=
    (by norm_num only : (100 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have h101 : 101 ≤ X := by
    dsimp only [X]
    nlinarith only [hY, sq_nonneg (gaussianBridgeScale L - 100)]
  have hpos : 0 < X := (by norm_num only : (0 : ℝ) < 101).trans_le h101
  have hl : 14 ≤ v := by
    dsimp only [v, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (k131_radius_log_mem hL).1
  have h7 : Real.exp 7 ≤ X :=
    (Real.le_log_iff_exp_le hpos).mp ((by norm_num only : (7 : ℝ) ≤ 14).trans hl)
  have hweight : 0 ≤ k131TailWeight X :=
    mul_nonneg (Real.rpow_nonneg hpos.le _) (k131_tail_fourier_signs hl).1
  have hψ := tail_psi_rh hRH h101 ((by norm_num only : (1 : ℝ) ≤ 14).trans hl)
  have he := mul_le_mul_of_nonneg_right ((neg_le_abs _).trans hψ) hweight
  have hs :
    Real.sqrt X * v ^ 2 / 24 * k131TailWeight X =
      Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v) / 24 := by
    rw [k131TailWeight, Real.sqrt_eq_rpow]
    have hp : X ^ (1 / 2 : ℝ) * X ^ (-(35 / 16 : ℝ)) = Real.exp (-(27 / 16 : ℝ) * v) := by
      rw [← Real.rpow_add hpos, show (1 / 2 : ℝ) + -(35 / 16) = -(27 / 16) by norm_num only,
        Real.rpow_def_of_pos hpos, mul_comm]
    change X ^ (1 / 2 : ℝ) * v ^ 2 / 24 * (X ^ (-(35 / 16 : ℝ)) * P.eval v) = _
    rw [← hp]
    ring
  change
    -(Chebyshev.psi X - X) * k131TailWeight X ≤ Real.sqrt X * v ^ 2 / 24 * k131TailWeight X at he
  rw [hs] at he
  have ht := k131_trace_tail_rh_le a b c hRH h7 h101 hl htrace
  dsimp only [v, P, D] at hs he ⊢
  linarith only [ht, he]

/-- For three primitive real even characters which are trivial on the tested
primes, the combined oscillating zero sum admits the explicit Euler-tail bound. -/
theorem k131_three_zero_upper {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hp : 2 ≤ p) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (hG : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := gaussianBridgeScale L ^ 2
    let v := Real.log X
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    let B := k131CosineCore (Real.log p + Real.log q + Real.log r)
    (-(∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm a X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm b X ρ).re -
        (∑' ρ : ℂ, k131MellinKernel.oscillatingZeroTerm c X ρ).re ≤
      B 0 + k131GramMix B - (k131ShiftedGram a L + k131ShiftedGram b L + k131ShiftedGram c L) +
        4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6) := by
  intro X v P D B
  have hy : 0 < gaussianBridgeScale L :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have hv : 14 ≤ v := by
    dsimp only [v, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (k131_radius_log_mem hL).1
  have h7 : Real.exp 7 ≤ X :=
    (Real.le_log_iff_exp_le (pow_pos hy 2)).mp ((by norm_num only : (7 : ℝ) ≤ 14).trans hv)
  have hz := k131_three_gram_upper ha hb hc hp hq hr hG hL hpa hpb hpc
  have he := k131_combined_euler_tail a b c h7
  have ht := k131_bridge_trace_tail_le a b c hG.riemann hL htrace
  dsimp only at ht hz
  dsimp only [X, v, P, D, B] at he ⊢
  rw [he] at ht
  linarith only [hz, ht]

/-- The pole and conductor contribution to the K131 cosine core at frequency
`t`, with the xi term removed. -/
@[expose]
noncomputable def k131PoleConductor (L t : ℝ) : ℝ :=
  let y := Real.exp |t|
  let H := fun u : ℝ ↦ (k131MassFn (u : ℂ) * (y : ℂ) ^ (u : ℂ)).re
  (-3 * (H (-1 / 2) + H (1 / 2)) + L * k131MassProfile y⁻¹)

private theorem gram_mix_mul (a : ℝ) (F : ℝ → ℝ) :
    k131GramMix (fun t ↦ a * F t) = a * k131GramMix F := by
  simp only [k131GramMix, mul_sub, Finset.mul_sum, Finset.sum_mul, div_eq_mul_inv]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Under RH the combined core is bounded by its exact pole and conductor
contribution plus the uniform xi allowance. -/
theorem k131_core_le_poles (hRH : RiemannHypothesis) (L : ℝ) :
    k131CosineCore L 0 + k131GramMix (k131CosineCore L) ≤
      k131PoleConductor L 0 + k131GramMix (k131PoleConductor L) + 21 / 10000 := by
  have he : k131CosineCore L = fun t ↦ 3 * k131CosineXi |t| + k131PoleConductor L t := by
    funext t
    dsimp only [k131CosineCore, k131PoleConductor]
    ring
  rw [he, k131_gram_mix_add, gram_mix_mul]
  simp only [abs_zero]
  linarith only [(le_abs_self _).trans (k131_xi_gram_cap hRH)]

private theorem mass_at_half : k131MassFn (1 / 2) = (halfLineMass : ℂ) := by
  rw [k131_mass_denominator _ (by norm_num only)]
  simp only [halfLineMass, kernelNumerator, k131Numerator, Complex.ofReal_ratCast, Rat.cast_div,
    Rat.cast_mul, Rat.cast_sub, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat, Rat.cast_one]
  norm_num only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow]
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ratCast]
  ring

private theorem mass_half_scaled (t u : ℝ) (hu : k131MassFn (u : ℂ) = (halfLineMass : ℂ)) :
    (k131MassFn (u : ℂ) * ((Real.exp |t| : ℝ) : ℂ) ^ (u : ℂ)).re =
      halfLineMass * Real.exp (|t| * u) := by
  rw [hu, ← Complex.ofReal_cpow (Real.exp_pos _).le, ← Complex.ofReal_mul, Complex.ofReal_re,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]

/-- The explicit pole and conductor term equals the hyperbolic cosine
pole value plus one quarter of the Fourier mass times the conductor logarithm. -/
private theorem k131_pole_conductor_eval (L t : ℝ) :
    k131PoleConductor L t = -6 * halfLineMass * Real.cosh (t / 2) + L * fourierMass t / 4 := by
  have hp : k131MassFn ((1 / 2 : ℝ) : ℂ) = (halfLineMass : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using mass_at_half
  have hn : k131MassFn ((-1 / 2 : ℝ) : ℂ) = (halfLineMass : ℂ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Complex.ofReal_neg, k131_mass_even, hp]
  have hm : k131MassProfile (Real.exp |t|)⁻¹ = fourierMass t / 4 := by
    rw [k131_mass_profile_fourier, Real.log_inv, Real.log_exp, abs_neg, abs_abs, fourierMass]
    ring
  simp only [k131PoleConductor, mass_half_scaled t _ hn, mass_half_scaled t _ hp, hm]
  have hc : Real.cosh (|t| / 2) = Real.cosh (t / 2) := by
    rw [← Real.cosh_abs (t / 2), abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  rw [Real.cosh_eq] at hc
  rw [← hc, show |t| * (-1 / 2 : ℝ) = -(|t| / 2) by ring, show |t| * (1 / 2 : ℝ) = |t| / 2 by ring]
  ring

private theorem gram_mix_fourier_mass : k131GramMix fourierMass = -shiftedConductor := by
  have hf (i j : Fin 4) : k131GramFreq i - k131GramFreq j = offsets i - offsets j := by
    simp only [k131GramFreq]
    ring
  simp only [k131GramMix, shiftedConductor, hf, k131GramCoeff, ← Finset.sum_div]
  simp only [k131GramFreq]
  ring

private theorem gram_mix_half_poles :
    k131GramMix (fun t : ℝ ↦ -6 * halfLineMass * Real.cosh (t / 2)) =
      -reflectedConstant - 3 * (2 * gramAbsMass + gramAbsMass ^ 2 / 2) / 100000 := by
  have hf (i j : Fin 4) : k131GramFreq i - k131GramFreq j = offsets i - offsets j := by
    simp only [k131GramFreq]
    ring
  rw [gram_mix_mul]
  simp only [k131GramMix, reflectedConstant, hf, k131GramCoeff]
  simp only [k131GramFreq]
  ring

private theorem k131_core_scalar_eval (L : ℝ) :
    k131PoleConductor L 0 + k131GramMix (k131PoleConductor L) =
      -6 * halfLineMass - reflectedConstant - 3 * (2 * gramAbsMass + gramAbsMass ^ 2 / 2) / 100000 +
        L * k131Beta / 4 := by
  have he :
    k131PoleConductor L = fun t ↦
      -6 * halfLineMass * Real.cosh (t / 2) + (L / 4) * fourierMass t := by
    funext t
    rw [k131_pole_conductor_eval]
    ring
  have h0 : fourierMass 0 = 3 / 4 := by
    simp only [fourierMass, abs_zero, mul_zero, Real.exp_zero, mul_one,
      ← Polynomial.coeff_zero_eq_eval_zero, coeff_fourier, fourierCoeff]
    norm_num only [List.getD_cons_zero, Rat.cast_div, Rat.cast_ofNat]
  rw [k131_pole_conductor_eval, he, k131_gram_mix_add, gram_mix_half_poles, gram_mix_mul,
    gram_mix_fourier_mass, h0]
  simp only [zero_div, Real.cosh_zero, mul_one, k131Beta]
  ring

private theorem moment_poly_add (P Q : Polynomial ℝ) (r : ℝ) (m : ℕ) :
    k131MomentPoly (P + Q) r m = k131MomentPoly P r m + k131MomentPoly Q r m := by
  have he (j : ℕ) :
    (Polynomial.derivative^[j]) (P + Q) =
      (Polynomial.derivative^[j]) P + (Polynomial.derivative^[j]) Q := by
    induction j with
    | zero => rfl
    | succ j hj => simp only [Function.iterate_succ_apply', hj, Polynomial.derivative_add]
  simp only [k131MomentPoly, he, mul_add, Finset.sum_add_distrib]

private theorem main_tail_poly_add (P Q : Polynomial ℝ) :
    mainTailPoly (P + Q) = mainTailPoly P + mainTailPoly Q := by
  simp only [mainTailPoly, gammaMainPoly, Polynomial.derivative_add, mul_add, add_sub_add_comm,
    moment_poly_add]
  ring

private theorem tail_rate_eq {y : ℝ} (hy : 0 < y) (r : ℝ) :
    Real.exp (-r * Real.log (y ^ 2)) = y ^ (-(2 * r)) := by
  rw [Real.log_pow, Nat.cast_ofNat, Real.rpow_def_of_pos hy]
  congr 1
  ring

private theorem k131_tail_scalar_eval {y : ℝ} (hy : 0 < y) :
    let v := Real.log (y ^ 2)
    let P := gaussianK131Fourier + k131GramEulerPoly
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    4 * Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly P (19 / 16) 0).eval v +
        Real.exp (-(27 / 16 : ℝ) * v) * (v ^ 2 * P.eval v + (k131MomentPoly D (27 / 16) 0).eval v) /
          6 =
      logPowerPoly (-(19 / 8 : ℝ))
          (Polynomial.C 4 * k131MomentPoly (gaussianK131Fourier + gramFourier) (19 / 16) 0) y +
        logPowerPoly (-(27 / 8 : ℝ))
          (Polynomial.C (1 / 6) * (mainTailPoly gaussianK131Fourier + mainTailPoly gramFourier))
          y := by
  intro v P D
  have h19 := tail_rate_eq hy (19 / 16)
  have h27 := tail_rate_eq hy (27 / 16)
  norm_num only at h19 h27
  dsimp only [v, P, D, k131GramEulerPoly]
  rw [h19, h27, ← main_tail_poly_add, Real.log_pow, Nat.cast_ofNat]
  simp only [logPowerPoly, mainTailPoly, gammaMainPoly, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
  ring

private theorem k131_affine_conductor (L : ℝ) :
    2 * L * k131Beta / 4 =
      (gaussianBridgeScale L + 123 / 10) * (k131Beta / (2 * (519674 / 1000000))) := by
  rw [gaussianBridgeScale]
  ring

/-- The unsigned forward sum at a shifted radius is its smooth mass plus
the lower endpoint weight, with the centered Chebyshev derivative integral subtracted. -/
theorem k131_shift_forward_abel {y : ℝ} (hy : 0 < y) (hy₁ : 1 ≤ y ^ 2) :
    let u := y ^ 2 * Real.exp (9 / 4)
    let f := k131ForwardWeight y
    (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      (∫ t in (1 : ℝ)..u, f t) + f 1 - ∫ t in (1 : ℝ)..u, (Chebyshev.psi t - t) * deriv f t := by
  intro u f
  have hu : 1 ≤ u :=
    hy₁.trans
      (le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 9 / 4)))
  have hd (t : ℝ) (ht : t ∈ Set.Icc (1 : ℝ) u) :=
    forward_weight_deriv hy (zero_lt_one.trans_le ht.1)
  have hc : ContinuousOn (deriv f) (Set.Icc (1 : ℝ) u) := fun t ht ↦
    (forward_slope_continuous hy (zero_lt_one.trans_le ht.1)).continuousWithinAt
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval (f := f)
      (by norm_num only : (0 : ℝ) ≤ 1) hu (fun t ht ↦ (hd t ht).differentiableAt)
      hc.integrableOn_Icc
  have hfloor : (1 : ℕ) ≤ ⌊u⌋₊ := Nat.le_floor (by simpa only [Nat.cast_one] using hu)
  rw [Nat.floor_one, Chebyshev.psi_one, show f u = 0 from forward_weight_right hy] at h
  rw [sum_prefix_tail hfloor]
  have hs : Finset.Icc (0 : ℕ) 1 = {0, 1} := by decide
  simp only [hs, Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)), Finset.sum_singleton,
    ArithmeticFunction.map_zero, ArithmeticFunction.vonMangoldt_apply_one, mul_zero, add_zero,
    zero_add]
  have he :
    (∑ n ∈ Finset.Ioc 1 ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 1 ⌊u⌋₊, ArithmeticFunction.vonMangoldt n * f n :=
    Finset.sum_congr rfl (fun _ _ ↦ mul_comm _ _)
  rw [he]
  linarith only [h]

/-- The shifted forward sum has a closed-form smooth mass at its support
endpoint and at one, with the remaining Chebyshev error retained as an integral. -/
theorem k131_shift_forward_eval {y : ℝ} (hy : 0 < y) (hy₁ : 1 ≤ y ^ 2) :
    let u := y ^ 2 * Real.exp (9 / 4)
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
    (∑ n ∈ Finset.Icc 0 ⌊u⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      (gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) *
            (Q.eval 0 - Real.exp (-(35 / 16 : ℝ) * z) * Q.eval z) +
          f 1 -
        ∫ t in (1 : ℝ)..u, (Chebyshev.psi t - t) * deriv f t := by
  intro u z f Q
  have hu : 1 ≤ u :=
    hy₁.trans
      (le_mul_of_one_le_right (sq_nonneg _) (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 9 / 4)))
  have h0 : forwardCoord y u = 0 := by
    dsimp only [u, forwardCoord]
    rw [mul_div_cancel_left₀ _ (pow_pos hy 2).ne', Real.log_exp, sub_self]
  have hz : forwardCoord y 1 = z := by
    dsimp only [forwardCoord, z]
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat, sub_neg_eq_add]
  have h := k131_shift_forward_abel hy hy₁
  dsimp only at h
  change _ = (∫ t in (1 : ℝ)..u, k131ForwardWeight y t) + _ - _ at h
  rw [k131_mass_log_interval hy zero_lt_one hu, h0, hz] at h
  simp only [← gaussian_k131_inverse_eval] at h
  rw [k131_exp_poly_integral forward_inverse_degree (by norm_num only : (35 / 16 : ℝ) ≠ 0),
    mul_zero, Real.exp_zero, one_mul] at h
  exact h

/-- At each K131 Gram frequency the shifted forward sum can be removed
from the contour difference in favor of its moment and Chebyshev error. -/
theorem k131_shifted_difference_eval {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (i : Fin 4) :
    let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
    let y := Real.sqrt x
    let z := 9 / 4 + 2 * Real.log y
    let f := k131ForwardWeight y
    let Q := k131MomentPoly gaussianK131InversePoly (35 / 16) 0
    k131ShiftedDifference χ L i =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re + (k131ReflectedIntegral χ x).re +
          (k131GammaIntegral χ x).re -
        ((gaussianK131Amplitude : ℝ) * y * Real.exp (9 / 8) *
              (Q.eval 0 - Real.exp (-(35 / 16 : ℝ) * z) * Q.eval z) +
            f 1 -
          ∫ t in (1 : ℝ)..x * Real.exp (9 / 4), (Chebyshev.psi t - t) * deriv f t) := by
  intro x y z f Q
  have hx : 1 ≤ x := k131_gram_shifted_scale hL i
  have hy : 0 < y := Real.sqrt_pos.2 (zero_lt_one.trans_le hx)
  have hs : y ^ 2 = x := Real.sq_sqrt (zero_le_one.trans hx)
  have he := k131_shift_forward_eval hy (hs.symm ▸ hx)
  dsimp only at he
  rw [hs] at he
  unfold k131ShiftedDifference
  dsimp only [x, y, z, f, Q] at he ⊢
  rw [he]

/-- The shifted reflected Euler trace deficit based at the main cutoff
`X` with logarithmic displacement `h`. -/
@[expose]
noncomputable def k131AuxReflect (α : ℕ → ℝ) (X h : ℝ) : ℝ :=
  ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))) *
    ∑' n : { n : ℕ // ⌊X⌋₊ < n },
      α n.val *
        (ArithmeticFunction.vonMangoldt n.val *
          ((n.val : ℝ) ^ (-(35 / 16 : ℝ)) * gaussianK131Inverse (Real.log X - h + Real.log n.val)))

private theorem aux_reflect_summable {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4) (X h : ℝ) :
    Summable
      (fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
        α n.val *
          (ArithmeticFunction.vonMangoldt n.val *
            ((n.val : ℝ) ^ (-(35 / 16 : ℝ)) *
              gaussianK131Inverse (Real.log X - h + Real.log n.val)))) := by
  let P := gaussianK131InversePoly.comp (Polynomial.C (Real.log X - h) + Polynomial.X)
  have hs := (tail_mangoldt_poly_summable P).subtype (fun n : ℕ ↦ ⌊X⌋₊ < n)
  refine (hs.norm.mul_left 4).of_norm_bounded (fun n ↦ ?_)
  simp only [Function.comp_apply, P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_X, gaussian_k131_inverse_eval]
  rw [norm_mul, Real.norm_eq_abs (α n.val), abs_of_nonneg (hα _).1]
  exact mul_le_mul_of_nonneg_right (hα _).2 (norm_nonneg _)

/-- Moving to a larger displacement decreases the reflected trace deficit
after removing its change of exponential scale. -/
theorem k131_aux_reflect_compare {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4) {X u v : ℝ}
    (huv : u ≤ v) (hv : v ≤ Real.log X) :
    Real.exp (-(27 / 16 : ℝ) * (v - u)) * k131AuxReflect α X v ≤ k131AuxReflect α X u := by
  have hmono {z w : ℝ} (hz : 0 ≤ z) (hzw : z ≤ w) :
    gaussianK131Inverse z ≤ gaussianK131Inverse w := by
    unfold gaussianK131Inverse
    exact
      Finset.sum_le_sum
        (fun j _ ↦
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzw _) (inverse_coeff_nonneg_kernel j))
  unfold k131AuxReflect
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hm :=
    (aux_reflect_summable hα X v).tsum_le_tsum (g := fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
      α n.val *
        (ArithmeticFunction.vonMangoldt n.val *
          ((n.val : ℝ) ^ (-(35 / 16 : ℝ)) * gaussianK131Inverse (Real.log X - u + Real.log n.val))))
      (fun n ↦ by
        have hz : 0 ≤ Real.log X - v + Real.log n.val :=
          add_nonneg (sub_nonneg.mpr hv) (Real.log_natCast_nonneg n.val)
        have hn :=
          hmono hz
            (by linarith only [huv] :
              Real.log X - v + Real.log n.val ≤ Real.log X - u + Real.log n.val)
        exact
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg (Nat.cast_nonneg _) _))
              ArithmeticFunction.vonMangoldt_nonneg)
            (hα _).1)
      (aux_reflect_summable hα X u)
  let A := (gaussianK131Amplitude : ℝ)
  let E := fun h : ℝ ↦ Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))
  let c := Real.exp (-(27 / 16 : ℝ) * (v - u))
  have he : c * E v = E u := by
    dsimp only [c, E]
    rw [← Real.exp_add]
    congr 1
    ring
  have hf (w : ℝ) : c * (A * E v * w) = A * E u * w := by
    rw [← he]
    ring
  rw [hf]
  exact mul_le_mul_of_nonneg_left hm (mul_nonneg hA (Real.exp_pos _).le)

/-- Each positive reflected Gram term absorbs part of its paired negative
term, leaving the two reflection weights from the K131 scalar comparison. -/
theorem k131_aux_reflect_pair_le {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4) {X : ℝ}
    (hX : 9 / 2 ≤ Real.log X) :
    -(973 / 5000 - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10))) *
          k131AuxReflect α X (1 / 10) -
        (13 / 1250 - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))) * k131AuxReflect α X (9 / 2) ≤
      1831 / 10000 * k131AuxReflect α X 0 - 973 / 5000 * k131AuxReflect α X (1 / 10) +
          1 / 80 * k131AuxReflect α X (21 / 10) -
        13 / 1250 * k131AuxReflect α X (9 / 2) := by
  have h₁ :=
    k131_aux_reflect_compare hα (u := 0) (v := 1 / 10) (by norm_num only)
      ((by norm_num only : (1 / 10 : ℝ) ≤ 9 / 2).trans hX)
  have h₂ := k131_aux_reflect_compare hα (u := 21 / 10) (v := 9 / 2) (by norm_num only) hX
  rw [sub_zero] at h₁
  rw [show (9 / 2 : ℝ) - 21 / 10 = 12 / 5 by norm_num only] at h₂
  linarith only [h₁, h₂]

/-- The reflected profile at the shifted contour scale gives the exact
auxiliary Euler tail once the trace deficit vanishes below the main cutoff. -/
theorem k131_aux_reflect_eq_tsum {α : ℕ → ℝ} {X h : ℝ} (hX : 0 < X)
    (hx : 1 ≤ X * Real.exp (-(9 / 4 + h)))
    (hsmall : ∀ n : ℕ, (n : ℝ) ≤ X → α n * ArithmeticFunction.vonMangoldt n = 0) :
    let x := X * Real.exp (-(9 / 4 + h))
    k131AuxReflect α X h =
      ∑' n : ℕ,
        α n * ArithmeticFunction.vonMangoldt n *
          (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n) := by
  intro x
  have hz : 9 / 4 + Real.log x = Real.log X - h := by
    dsimp only [x]
    rw [Real.log_mul hX.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  let F := fun n : ℕ ↦
    α n * ArithmeticFunction.vonMangoldt n * (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n)
  have hs : Function.support F ⊆ {n : ℕ | ⌊X⌋₊ < n} := by
    intro n hn
    by_contra h
    have hle : n ≤ ⌊X⌋₊ := Nat.le_of_not_gt h
    exact hn (by simp only [F, hsmall n ((Nat.le_floor_iff hX.le).mp hle), zero_mul])
  change k131AuxReflect α X h = ∑' n : ℕ, F n
  rw [← tsum_subtype_eq_of_support_subset hs, k131AuxReflect, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hn : 1 ≤ (n.val : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.zero_le _ |>.trans_lt n.property)
  dsimp only [F]
  rw [k131_dual_profile_eq hx hn]
  rw [hz]
  ring

private theorem k131_dual_real_sum {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n)
    HasSum (fun n : ℕ ↦ (χ n).re * W n)
      (∑' n : ℕ,
          ((χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) / (n : ℂ) ^ (1 / 2 : ℂ)) *
            (k131MellinProfile (((n : ℝ) * x)⁻¹) : ℂ)).re := by
  intro W
  have h :=
    k131_dual_euler_summable hx
      (χ.LSeriesSummable_twist_vonMangoldt (by norm_num only [Complex.ofReal_re]))
  exact (Complex.hasSum_re h.hasSum).congr_fun (fun n ↦ (k131_dual_char_term_re χ x n).symm)

/-- A primitive self-inverse character that is trivial on the tested primes
has a reflected contour equal to its Gamma term minus the principal sum plus its deficit. -/
theorem k131_aux_reflected_split {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hn : χ ≠ 1) (hi : χ⁻¹ = χ) {X h : ℝ} (hX : 0 < X)
    (hx : 1 ≤ X * Real.exp (-(9 / 4 + h))) (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ X → χ p = 1) :
    let x := X * Real.exp (-(9 / 4 + h))
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n)
    (k131ReflectedIntegral χ x).re =
      (k131ReflectedGamma χ x).re - (∑' n : ℕ, W n) +
        k131AuxReflect (fun n ↦ 1 - (χ n).re) X h := by
  intro x W
  have hx₀ := zero_lt_one.trans_le hx
  have hprincipal := k131_dual_real_sum (1 : DirichletCharacter ℂ 1) hx₀
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re,
    one_mul] at hprincipal
  have hχ := k131_dual_real_sum χ hx₀
  have hsmall (n : ℕ) (hle : (n : ℝ) ≤ X) :
    (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n = 0 := by
    by_cases hm : ArithmeticFunction.vonMangoldt n = 0
    · rw [hm, mul_zero]
    rw [AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero χ ht hle hm,
      Complex.one_re, sub_self, zero_mul]
  have he := k131_aux_reflect_eq_tsum hX hx hsmall
  dsimp only at he
  have hs :=
    (hprincipal.sub hχ).congr_fun
      (fun n ↦ by
        change (1 - (χ n).re) * W n = W n - (χ n).re * W n
        rw [sub_mul, one_mul])
  have hde := hs.tsum_eq
  rw [k131_reflected_eq_dual hp hn (hi.symm ▸ hn) hx₀, hi, Complex.sub_re]
  rw [he]
  simp only [mul_assoc] at hde ⊢
  linarith only [hde, hprincipal.tsum_eq]

private theorem k131_aux_reflect_add_three {α β γ : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hβ : ∀ n, β n ∈ Set.Icc (0 : ℝ) 4) (hγ : ∀ n, γ n ∈ Set.Icc (0 : ℝ) 4) (X h : ℝ) :
    k131AuxReflect (fun n ↦ α n + β n + γ n) X h =
      k131AuxReflect α X h + k131AuxReflect β X h + k131AuxReflect γ X h := by
  simp only [k131AuxReflect, add_mul]
  rw [((aux_reflect_summable hα X h).add (aux_reflect_summable hβ X h)).tsum_add
      (aux_reflect_summable hγ X h),
    (aux_reflect_summable hα X h).tsum_add (aux_reflect_summable hβ X h), mul_add, mul_add]

private theorem char_gap_mem {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    1 - (χ n).re ∈ Set.Icc (0 : ℝ) 4 := by
  have h := abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))
  exact ⟨sub_nonneg.mpr h.2, by linarith only [h.1]⟩

/-- At a shifted scale the three reflected integrals share one principal
Euler series and one trace deficit above the tested prime range. -/
theorem k131_three_aux_reflected_split {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c) {X h : ℝ} (hX : 0 < X)
    (hx : 1 ≤ X * Real.exp (-(9 / 4 + h)))
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1 ∧ b l = 1 ∧ c l = 1) :
    let x := X * Real.exp (-(9 / 4 + h))
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n)
    (k131ReflectedIntegral a x + k131ReflectedIntegral b x + k131ReflectedIntegral c x).re =
      (k131ReflectedGamma a x + k131ReflectedGamma b x + k131ReflectedGamma c x).re -
          3 * (∑' n : ℕ, W n) +
        k131AuxReflect (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) X h := by
  intro x W
  have h₁ := k131_aux_reflected_split ha.1 ha.2.1 ha.2.2 hX hx (fun l hl hle ↦ (ht l hl hle).1)
  have h₂ := k131_aux_reflected_split hb.1 hb.2.1 hb.2.2 hX hx (fun l hl hle ↦ (ht l hl hle).2.1)
  have h₃ := k131_aux_reflected_split hc.1 hc.2.1 hc.2.2 hX hx (fun l hl hle ↦ (ht l hl hle).2.2)
  have hsum := k131_aux_reflect_add_three (char_gap_mem a) (char_gap_mem b) (char_gap_mem c) X h
  have he :
    (fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)) = fun n : ℕ ↦
      (1 - (a n).re) + (1 - (b n).re) + (1 - (c n).re) := by
    funext n
    ring
  rw [he, hsum]
  simp only [Complex.add_re, x, W]
  linarith only [h₁, h₂, h₃]

/-- The signed sum of the four reflected trace deficits in the Gram
comparison is bounded below by the two effective negative terms. -/
theorem k131_gram_aux_reflect_lower {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4) {X : ℝ}
    (hX : 9 / 2 ≤ Real.log X) :
    -(973 / 5000 - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10))) *
          k131AuxReflect α X (1 / 10) -
        (13 / 1250 - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))) * k131AuxReflect α X (9 / 2) ≤
      ∑ i : Fin 4, k131GramCoeff i * k131AuxReflect α X (k131GramFreq i - 9 / 4) := by
  have he (i : Fin 4) : k131GramFreq i - 9 / 4 = offsets i := by
    rw [k131GramFreq, add_sub_cancel_left]
  simp only [he, k131GramCoeff, gram, offsets, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  linarith only [k131_aux_reflect_pair_le hα hX]

/-- On the K131 bridge the reflected parts of all four shifted contours
share the two-term deficit lower bound, after subtracting their principal parts. -/
theorem k131_gram_reflected_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := gaussianBridgeScale L ^ 2
    let x := fun i ↦ X * Real.exp (-(k131GramFreq i))
    let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-(973 / 5000 - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10))) *
          k131AuxReflect α X (1 / 10) -
        (13 / 1250 - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))) * k131AuxReflect α X (9 / 2) ≤
      ∑ i : Fin 4,
        k131GramCoeff i *
          ((k131ReflectedIntegral a (x i) + k131ReflectedIntegral b (x i) +
                  k131ReflectedIntegral c (x i)).re -
              (k131ReflectedGamma a (x i) + k131ReflectedGamma b (x i) +
                  k131ReflectedGamma c (x i)).re +
            3 *
              ∑' n : ℕ,
                ArithmeticFunction.vonMangoldt n *
                  (k131MellinProfile (((n : ℝ) * x i)⁻¹) / Real.sqrt n))) := by
  intro X x α
  have hy : 0 < gaussianBridgeScale L :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  have hl : 9 / 2 ≤ Real.log X := by
    dsimp only [X]
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (by norm_num only : (9 / 2 : ℝ) ≤ 14).trans (k131_radius_log_mem hL).1
  have hα (n : ℕ) : α n ∈ Set.Icc (0 : ℝ) 4 := by
    dsimp only [α]
    exact
      ⟨by linarith only [(char_gap_mem a n).1, (char_gap_mem b n).1, (char_gap_mem c n).1], by
        linarith only [htrace n]⟩
  refine (k131_gram_aux_reflect_lower hα hl).trans_eq (Finset.sum_congr rfl (fun i _ ↦ ?_))
  have he : 9 / 4 + (k131GramFreq i - 9 / 4) = k131GramFreq i := by ring
  have hx : 1 ≤ X * Real.exp (-(9 / 4 + (k131GramFreq i - 9 / 4))) := by
    rw [he]
    exact k131_gram_shifted_scale hL i
  have h := k131_three_aux_reflected_split ha hb hc (pow_pos hy 2) hx ht
  dsimp only at h
  rw [he] at h
  dsimp only [x, α]
  congr 1
  linarith only [h]

/-- A nonnegative trace deficit bounded by four costs at most four times
the unsigned Mangoldt tail with the shifted inverse polynomial. -/
theorem k131_aux_reflect_le_mangoldt {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4) {X h : ℝ}
    (hlog : h ≤ Real.log X) :
    let P := gaussianK131InversePoly.comp (Polynomial.C (Real.log X - h) + Polynomial.X)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((n : ℝ) ^ (-(35 / 16 : ℝ)) * P.eval (Real.log n))
    k131AuxReflect α X h ≤
      4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))) *
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) := by
  intro P f
  have hf : Summable f := tail_mangoldt_poly_summable P
  have he (n : ℕ) : P.eval (Real.log n) = gaussianK131Inverse (Real.log X - h + Real.log n) := by
    simp only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      gaussian_k131_inverse_eval]
  have hnon (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    rw [he]
    exact
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
          (k131_inverse_nonneg (add_nonneg (sub_nonneg.mpr hlog) (Real.log_natCast_nonneg n))))
  have hs :=
    (aux_reflect_summable hα X h).tsum_le_tsum (g := fun n : { n : ℕ // ⌊X⌋₊ < n } ↦ 4 * f n.val)
      (fun n ↦ by
        rw [← he]
        exact mul_le_mul_of_nonneg_right (hα n.val).2 (hnon n.val))
      ((hf.subtype (fun n : ℕ ↦ ⌊X⌋₊ < n)).mul_left 4)
  rw [tsum_mul_left,
    k131_tail_subtype_eq hf (by simp only [f, ArithmeticFunction.map_zero, zero_mul])] at hs
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  unfold k131AuxReflect
  let C := (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))
  rw [mul_comm (4 : ℝ) C, mul_assoc C 4]
  exact mul_le_mul_of_nonneg_left hs (mul_nonneg hA (Real.exp_pos _).le)

/-- Above logarithmic height nine, the inverse polynomial's derivative
is dominated by `35/16` times its value, as required for the reflected tail. -/
theorem k131_inverse_slope_le {z : ℝ} (hz : 9 ≤ z) :
    gaussianK131InversePoly.derivative.eval z ≤ (35 / 16 : ℝ) * gaussianK131InversePoly.eval z := by
  simp only [gaussianK131InversePoly, Polynomial.derivative_sum, Polynomial.derivative_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  let k := 2 * j.val + 2
  have hk : k + 1 ≤ 19 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt)) 3
  have hcast : (↑(k + 1) : ℝ) ≤ 19 := by exact_mod_cast hk
  have h : (↑(k + 1) : ℝ) ≤ (35 / 16 : ℝ) * z := by linarith only [hz, hcast]
  have hpos : 0 ≤ (inverseCoeffs j : ℝ) * z ^ k :=
    mul_nonneg (inverse_coeff_nonneg_kernel j) (pow_nonneg (by linarith only [hz]) k)
  have hm := mul_le_mul_of_nonneg_left h hpos
  change
    (inverseCoeffs j : ℝ) * (↑(k + 1) : ℝ) * z ^ k ≤
      (35 / 16 : ℝ) * ((inverseCoeffs j : ℝ) * z ^ (k + 1))
  rw [pow_succ z k]
  nlinarith only [hm]

private theorem tail_poly_rh_majorant {P : Polynomial ℝ} (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 101 ≤ X) (hl : 1 ≤ Real.log X) :
    let f := fun t : ℝ ↦ t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t)
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    ∀ t ∈ Set.Ioi X,
      |(Chebyshev.psi t - t) * deriv f t| ≤ |t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t)| / 24 := by
  intro f D t ht
  have hXt : 101 ≤ t := hX.trans ht.le
  have hX₀ := (by norm_num only : (0 : ℝ) < 101).trans_le hX
  have ht₀ := hX₀.trans ht
  have hlog := hl.trans (Real.log_le_log hX₀ ht.le)
  rw [abs_mul, (tail_poly_weight_deriv P ht₀).deriv]
  refine (mul_le_mul_of_nonneg_right (tail_psi_rh hRH hXt hlog) (abs_nonneg _)).trans_eq ?_
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_sub, abs_mul, abs_of_nonneg (sq_nonneg (Real.log t)),
    abs_of_nonneg (Real.rpow_nonneg ht₀.le (-(51 / 16 : ℝ))),
    abs_of_nonneg (Real.rpow_nonneg ht₀.le (-(43 / 16 : ℝ))), abs_sub_comm]
  rw [Real.sqrt_eq_rpow]
  have hp : t ^ (1 / 2 : ℝ) * t ^ (-51 / 16 : ℝ) = t ^ (-43 / 16 : ℝ) := by
    rw [← Real.rpow_add ht₀]
    norm_num only
  ring_nf
  rw [← hp]
  ring

/-- For a logarithmic polynomial of degree below twenty, RH bounds the
Mangoldt tail by its exact main moment and an integrable derivative majorant. -/
theorem k131_poly_mangoldt_rh_le {P : Polynomial ℝ} (hP : P.natDegree < 20)
    (hRH : RiemannHypothesis) {X : ℝ} (hX : 101 ≤ X) (hl : 1 ≤ Real.log X) :
    let f := fun t : ℝ ↦ t ^ (-(35 / 16 : ℝ)) * P.eval (Real.log t)
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * f n) -
        (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n * f n) ≤
      Real.exp (-(19 / 16 : ℝ) * Real.log X) * (k131MomentPoly P (19 / 16) 0).eval (Real.log X) -
          (Chebyshev.psi X - X) * f X +
        ∫ t in Set.Ioi X, |t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t)| / 24 := by
  intro f D
  have hX₁ := (by norm_num only : (1 : ℝ) ≤ 101).trans hX
  have hX₀ := zero_lt_one.trans_le hX₁
  have hf := tail_poly_integrable P hX₁ (by norm_num only : (0 : ℝ) < 19 / 16)
  rw [show -(19 / 16 : ℝ) - 1 = -(35 / 16) by norm_num only] at hf
  have hi := tail_poly_integrable D hX₁ (by norm_num only : (0 : ℝ) < 27 / 16)
  rw [show -(27 / 16 : ℝ) - 1 = -(43 / 16) by norm_num only] at hi
  have hi' := hi.norm.div_const 24
  simp only [Real.norm_eq_abs] at hi'
  have hpt := tail_poly_rh_majorant (P := P) hRH hX hl
  have herr :
    MeasureTheory.IntegrableOn (fun t ↦ (Chebyshev.psi t - t) * deriv f t) (Set.Ioi X) := by
    refine
      hi'.mono'
        ((Chebyshev.psi_mono.measurable.sub measurable_id).mul
            (measurable_deriv f)).aestronglyMeasurable
        ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    exact hpt t ht
  have ha :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral hX₀.le (f := f)
      (fun _ _ _ ht ↦ (tail_poly_weight_deriv P (hX₀.trans_le ht.1)).differentiableAt)
      (fun _ _ ↦ (tail_poly_deriv_continuous P hX₀).integrableOn_Icc) hf herr
      (tail_poly_boundary_tendsto P) (tail_mangoldt_poly_summable P)
  have hm := k131_tail_poly_moment hP hX₁ (by norm_num only : (0 : ℝ) < 19 / 16)
  rw [show -(19 / 16 : ℝ) - 1 = -(35 / 16) by norm_num only] at hm
  have hb :=
    MeasureTheory.norm_integral_le_of_norm_le hi'
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        rw [Real.norm_eq_abs]
        exact hpt t ht)
  rw [Real.norm_eq_abs] at hb
  linarith only [ha, hm, (abs_le.mp hb).1]

/-- Under RH the shifted reflected deficit is bounded by four times the
main moment, the exact boundary correction and the positive derivative moment. -/
theorem k131_aux_reflect_rh_le {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {X h : ℝ} (hX : 101 ≤ X) (hl : 1 ≤ Real.log X)
    (hh : 0 ≤ Real.log X - h) (hz : 9 ≤ 2 * Real.log X - h) :
    let P := gaussianK131InversePoly.comp (Polynomial.C (Real.log X - h) + Polynomial.X)
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    k131AuxReflect α X h ≤
      4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))) *
        (Real.exp (-(19 / 16 : ℝ) * Real.log X) * (k131MomentPoly P (19 / 16) 0).eval (Real.log X) -
            (Chebyshev.psi X - X) * (X ^ (-(35 / 16 : ℝ)) * P.eval (Real.log X)) +
          ∫ t in Set.Ioi X, t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t) / 24) := by
  intro P D
  have hP : P.natDegree < 20 :=
    Nat.lt_succ_of_le
      (by
        dsimp only [P]
        rw [add_comm]
        exact degree_shift inverse_degree_le _)
  have hmain := k131_poly_mangoldt_rh_le hP hRH hX hl
  dsimp only at hmain
  have hX₀ := (by norm_num only : (0 : ℝ) < 101).trans_le hX
  have he :
    (∫ t in Set.Ioi X, |t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t)| / 24) =
      ∫ t in Set.Ioi X, t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t) / 24 := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have hl' := Real.log_le_log hX₀ ht.le
    have hsign :=
      k131_inverse_slope_le (by linarith only [hz, hl'] : 9 ≤ Real.log X - h + Real.log t)
    have hD : 0 ≤ D.eval (Real.log t) := by
      simp only [D, P, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_sub, Polynomial.eval_C, Polynomial.derivative_comp,
        Polynomial.derivative_add, Polynomial.derivative_C, Polynomial.derivative_X, zero_add,
        one_mul, Polynomial.eval_comp, Polynomial.eval_add]
      exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hsign)
    simp only [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (hX₀.trans ht).le (-(43 / 16 : ℝ))) hD)]
  rw [he] at hmain
  exact
    (k131_aux_reflect_le_mangoldt hα (sub_nonneg.mp hh)).trans
      (mul_le_mul_of_nonneg_left hmain
        (mul_nonneg (by norm_num only)
          (mul_nonneg (Rat.cast_nonneg.mpr (by decide +kernel)) (Real.exp_pos _).le)))

/-- A logarithmic power tail with polynomial weight is the finite sum
of the monomial logarithmic moments, with no degree restriction. -/
theorem k131_tail_finite_moments (P : Polynomial ℝ) {a r : ℝ} (ha : 1 ≤ a) (hr : 0 < r) :
    (∫ t in Set.Ioi a, t ^ (-r - 1) * P.eval (Real.log t)) =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        P.coeff k * (a ^ (-r) * Analysis.logPowerTailPoly r k (Real.log a)) := by
  have hP :
    ∀ t : ℝ,
      P.eval (Real.log t) = ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * Real.log t ^ k := by
    intro t
    conv_lhs => rw [P.as_sum_range_C_mul_X_pow' (Nat.lt_succ_self _)]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  simp only [hP, Finset.mul_sum]
  have he (k : ℕ) (t : ℝ) :
    t ^ (-r - 1) * (P.coeff k * Real.log t ^ k) = P.coeff k * (Real.log t ^ k * t ^ (-r - 1)) := by
    ring
  simp only [he]
  rw [MeasureTheory.integral_finsetSum _
      (fun k _ ↦ (Analysis.log_power_tail_integrable hr ha k).const_mul (P.coeff k))]
  apply Finset.sum_congr rfl
  intro k _
  rw [MeasureTheory.integral_const_mul, Analysis.log_power_tail_integral hr ha]

/-- The RH bound for the shifted reflected deficit contains only finite
logarithmic moments and the exact Chebyshev boundary value. -/
theorem k131_aux_reflect_moments_le {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {X h : ℝ} (hX : 101 ≤ X) (hl : 1 ≤ Real.log X)
    (hh : 0 ≤ Real.log X - h) (hz : 9 ≤ 2 * Real.log X - h) :
    let P := gaussianK131InversePoly.comp (Polynomial.C (Real.log X - h) + Polynomial.X)
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    k131AuxReflect α X h ≤
      4 * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (Real.log X - h))) *
        (Real.exp (-(19 / 16 : ℝ) * Real.log X) * (k131MomentPoly P (19 / 16) 0).eval (Real.log X) -
            (Chebyshev.psi X - X) * (X ^ (-(35 / 16 : ℝ)) * P.eval (Real.log X)) +
          (∑ k ∈ Finset.range (D.natDegree + 1),
              D.coeff k *
                (X ^ (-(27 / 16 : ℝ)) * Analysis.logPowerTailPoly (27 / 16) k (Real.log X))) /
            24) := by
  intro P D
  have hh' := k131_aux_reflect_rh_le hα hRH hX hl hh hz
  have hm :=
    k131_tail_finite_moments D ((by norm_num only : (1 : ℝ) ≤ 101).trans hX)
      (by norm_num only : (0 : ℝ) < 27 / 16)
  rw [show -(27 / 16 : ℝ) - 1 = -(43 / 16) by norm_num only] at hm
  rw [← hm, ← MeasureTheory.integral_div]
  exact hh'

private theorem tail_monomial_moment_zero {r : ℝ} (hr : r ≠ 0) (k : ℕ) :
    Analysis.logPowerTailPoly r k 0 = (k.factorial : ℝ) / r ^ (k + 1) := by
  induction k with
  | zero =>
    simp only [Analysis.logPowerTailPoly, Nat.factorial_zero, Nat.cast_one, zero_add, pow_one]
  | succ k
    hk =>
    rw [Analysis.logPowerTailPoly, zero_pow (Nat.succ_ne_zero _), zero_div, zero_add, hk,
      Nat.factorial_succ, Nat.cast_mul, pow_succ r (k + 1)]
    field_simp [hr]

private theorem tail_taylor_coeff (P : Polynomial ℝ) (z : ℝ) (k : ℕ) :
    ((k.factorial : ℝ) * (Polynomial.taylor z P).coeff k) =
      ((Polynomial.derivative^[k]) P).eval z := by
  rw [Polynomial.taylor_coeff]
  have h := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) (k := k)) P
  rw [← h]
  change _ = (k.factorial • Polynomial.hasseDeriv k P).eval z
  rw [Polynomial.eval_smul, nsmul_eq_mul]

/-- Evaluating a K131 moment polynomial is equivalent to integrating
the shifted polynomial against the exponential weight times a monomial. -/
theorem k131_shifted_exp_moment {P : Polynomial ℝ} (hP : P.natDegree < 20) {r : ℝ} (hr : 0 < r)
    (z : ℝ) (m : ℕ) :
    (∫ u in Set.Ioi (0 : ℝ), Real.exp (-r * u) * u ^ m * P.eval (z + u)) =
      (k131MomentPoly P r m).eval z := by
  let T := Polynomial.taylor z P
  have hT : T.natDegree < 20 := by simpa only [T, Polynomial.natDegree_taylor] using hP
  have he (u : ℝ) : P.eval (z + u) = ∑ k ∈ Finset.range 20, T.coeff k * u ^ k := by
    rw [add_comm, ← Polynomial.taylor_eval]
    exact T.eval_eq_sum_range' hT u
  simp only [he, Finset.mul_sum]
  have hf (k : ℕ) (u : ℝ) :
    Real.exp (-r * u) * u ^ m * (T.coeff k * u ^ k) =
      T.coeff k * (u ^ (k + m) * Real.exp (-r * u)) := by
    rw [pow_add]
    ring
  simp only [hf]
  rw [MeasureTheory.integral_finsetSum _
      (fun k _ ↦ (Analysis.exponential_moment_integrable hr (k + m)).const_mul _)]
  simp only [k131MomentPoly, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  rw [MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail hr (le_refl 0), mul_zero,
    Real.exp_zero, one_mul, tail_monomial_moment_zero hr.ne', ← tail_taylor_coeff]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp [hk]
  ring

private theorem shifted_moment_integrable (P : Polynomial ℝ) {r : ℝ} (hr : 0 < r) (z : ℝ) (m : ℕ) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-r * u) * u ^ m * P.eval (z + u))
      (Set.Ioi 0) := by
  let T := Polynomial.taylor z P
  have he (u : ℝ) :
    Real.exp (-r * u) * u ^ m * P.eval (z + u) =
      ∑ k ∈ Finset.range (T.natDegree + 1), T.coeff k * (u ^ (k + m) * Real.exp (-r * u)) := by
    rw [add_comm z, ← Polynomial.taylor_eval, T.eval_eq_sum_range' (Nat.lt_succ_self _) u,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [pow_add]
    ring
  simp only [he, MeasureTheory.IntegrableOn]
  exact
    MeasureTheory.integrable_finsetSum _
      (fun k _ ↦ (Analysis.exponential_moment_integrable hr (k + m)).const_mul _)

/-- A logarithmic-square tail of a translated polynomial equals its
three exponential moments of orders zero, one, and two. -/
theorem k131_tail_three_moments {P : Polynomial ℝ} (hP : P.natDegree < 20) {a r : ℝ} (ha : 0 < a)
    (hr : 0 < r) (z : ℝ) :
    let v := Real.log a
    (∫ t in Set.Ioi a, t ^ (-r - 1) * (Real.log t) ^ 2 * P.eval (z + Real.log t)) =
      a ^ (-r) *
        (v ^ 2 * (k131MomentPoly P r 0).eval (z + v) + 2 * v * (k131MomentPoly P r 1).eval (z + v) +
          (k131MomentPoly P r 2).eval (z + v)) := by
  intro v
  let g := fun x : ℝ ↦ Real.exp (-r * x) * x ^ 2 * P.eval (z + x)
  have hlog := MeasureTheory.integral_comp_log_Ioi g ha
  have he :
    (∫ t in Set.Ioi a, t ^ (-r - 1) * (Real.log t) ^ 2 * P.eval (z + Real.log t)) =
      ∫ t in Set.Ioi a, t⁻¹ * g (Real.log t) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht₀ := ha.trans ht
    simp only [g]
    rw [mul_comm (-r), ← Real.rpow_def_of_pos ht₀, Real.rpow_sub ht₀, Real.rpow_one, div_eq_mul_inv]
    ring
  rw [he]
  simp only [smul_eq_mul] at hlog
  rw [hlog]
  have himage : (fun u : ℝ ↦ u + v) '' Set.Ioi 0 = Set.Ioi v := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact lt_add_of_pos_left _ ht
    · intro hu
      exact ⟨u - v, sub_pos.mpr hu, sub_add_cancel _ _⟩
  rw [show Real.log a = v from rfl, ← himage]
  have ha' :
    (∫ y in (fun u : ℝ ↦ u + v) '' Set.Ioi 0, g y) = ∫ u in Set.Ioi (0 : ℝ), g (u + v) := by
    simpa only [id_eq, abs_one, one_smul] using
      MeasureTheory.integral_image_eq_integral_abs_deriv_smul (measurableSet_Ioi (a := (0 : ℝ)))
        (fun x _ ↦ ((hasDerivAt_id x).add_const v).hasDerivWithinAt)
        (fun _ _ _ _ h ↦ add_right_cancel h) g
  rw [ha']
  set w := z + v
  let F := fun m : ℕ ↦ fun u : ℝ ↦ Real.exp (-r * u) * u ^ m * P.eval (w + u)
  have hF (m : ℕ) : MeasureTheory.IntegrableOn (F m) (Set.Ioi 0) :=
    shifted_moment_integrable P hr w m
  have hg (u : ℝ) : g (u + v) = a ^ (-r) * (v ^ 2 * F 0 u + (2 * v) * F 1 u + F 2 u) := by
    simp only [g, F, w, pow_zero, pow_one, mul_one, mul_add, Real.exp_add, Real.rpow_def_of_pos ha,
      v, add_assoc, add_comm u]
    rw [mul_comm (Real.log a) (-r)]
    ring
  simp only [hg]
  have h0 := (hF 0).const_mul (v ^ 2)
  have h1 := (hF 1).const_mul (2 * v)
  have h01 : MeasureTheory.IntegrableOn (fun u ↦ v ^ 2 * F 0 u + 2 * v * F 1 u) (Set.Ioi 0) :=
    (h0.add h1).congr (Filter.Eventually.of_forall (fun _ ↦ rfl))
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add h01 (hF 2),
    MeasureTheory.integral_add h0 h1, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  simp only [F, k131_shifted_exp_moment hP hr]

private theorem k131_reflect_error_eval {X : ℝ} (hX : 0 < X) (h : ℝ) :
    let v := Real.log X
    let z := v - h
    let B := gaussianK131InversePoly
    let P := B.comp (Polynomial.C z + Polynomial.X)
    let D := Polynomial.X ^ 2 * (Polynomial.C (35 / 16 : ℝ) * P - P.derivative)
    let M := fun j ↦ k131MomentPoly (gammaMainPoly B) (27 / 16) j
    (∫ t in Set.Ioi X, t ^ (-(43 / 16 : ℝ)) * D.eval (Real.log t)) =
      X ^ (-(27 / 16 : ℝ)) *
        (v ^ 2 * (M 0).eval (z + v) + 2 * v * (M 1).eval (z + v) + (M 2).eval (z + v)) := by
  intro v z B P D M
  have hdeg : (gammaMainPoly B).natDegree < 20 := by
    apply Nat.lt_succ_of_le
    exact
      degree_sub (degree_mul_C inverse_degree_le (35 / 16 : ℝ))
        ((Polynomial.natDegree_derivative_le B).trans ((Nat.sub_le _ _).trans inverse_degree_le))
  have hs := k131_tail_three_moments hdeg hX (by norm_num only : (0 : ℝ) < 27 / 16) z
  dsimp only at hs
  rw [show -(27 / 16 : ℝ) - 1 = -(43 / 16) by norm_num only] at hs
  rw [← hs]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [D, P, gammaMainPoly, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_C, Polynomial.derivative_X, zero_add, one_mul, Polynomial.eval_comp,
    Polynomial.eval_add, mul_assoc]

private theorem k131_shifted_inverse_moment (z v : ℝ) :
    let P := gaussianK131InversePoly.comp (Polynomial.C z + Polynomial.X)
    (k131MomentPoly P (19 / 16) 0).eval v =
      (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (z + v) := by
  intro P
  have hp : P.natDegree < 20 :=
    Nat.lt_succ_of_le
      (by
        dsimp only [P]
        rw [add_comm]
        exact degree_shift inverse_degree_le _)
  have hr : (0 : ℝ) < 19 / 16 := by norm_num only
  rw [← k131_shifted_exp_moment hp hr, ←
    k131_shifted_exp_moment (Nat.lt_succ_of_le inverse_degree_le) hr]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [P, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
    add_assoc]

/-- The reflected tail majorant at cutoff `X` and displacement `h`,
formed from the main moment and the three RH error moments. -/
@[expose]
noncomputable def k131AuxReflectBound (X h : ℝ) : ℝ :=
  let v := Real.log X
  let w := 2 * v - h
  let B := gaussianK131InversePoly
  let H := Polynomial.C (35 / 16 : ℝ) * B - B.derivative
  let M := fun j ↦ k131MomentPoly H (27 / 16) j
  (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (v - h)) *
    (Real.exp (-(19 / 16 : ℝ) * v) * (k131MomentPoly B (19 / 16) 0).eval w +
      X ^ (-(27 / 16 : ℝ)) *
          (v ^ 2 * (B.eval w + (M 0).eval w) + 2 * v * (M 1).eval w + (M 2).eval w) /
        24)

/-- RH bounds the reflected trace deficit by four times the explicit
moment majorant whenever both shifted logarithmic arguments are in range. -/
theorem k131_aux_reflect_bound_le {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {X h : ℝ} (hX : 101 ≤ X) (hl : 1 ≤ Real.log X)
    (hh : 0 ≤ Real.log X - h) (hz : 9 ≤ 2 * Real.log X - h) :
    k131AuxReflect α X h ≤ 4 * k131AuxReflectBound X h := by
  let v := Real.log X
  let w := 2 * v - h
  let B := gaussianK131InversePoly
  have hX₀ := (by norm_num only : (0 : ℝ) < 101).trans_le hX
  have hw : v - h + v = w := by
    dsimp only [w]; ring
  have hB : 0 ≤ B.eval w := by
    rw [gaussian_k131_inverse_eval]
    exact k131_inverse_nonneg (by linarith only [hz])
  have hm := k131_aux_reflect_rh_le hα hRH hX hl hh hz
  dsimp only at hm
  rw [MeasureTheory.integral_div, k131_reflect_error_eval hX₀ h, k131_shifted_inverse_moment] at hm
  dsimp only at hm
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X] at hm
  rw [hw] at hm
  have hψ := (neg_le_abs (Chebyshev.psi X - X)).trans (tail_psi_rh hRH hX hl)
  have hbd :=
    mul_le_mul_of_nonneg_right hψ (mul_nonneg (Real.rpow_nonneg hX₀.le (-(35 / 16 : ℝ))) hB)
  have hp : Real.sqrt X * X ^ (-(35 / 16 : ℝ)) = X ^ (-(27 / 16 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hX₀]
    norm_num only
  have he :
    Real.sqrt X * v ^ 2 / 24 * (X ^ (-(35 / 16 : ℝ)) * B.eval w) =
      X ^ (-(27 / 16 : ℝ)) * (v ^ 2 * B.eval w) / 24 := by
    rw [← hp]
    ring
  rw [he] at hbd
  unfold k131AuxReflectBound
  refine hm.trans ?_
  dsimp only
  simp only [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only : (0 : ℝ) ≤ 4)
  apply
    mul_le_mul_of_nonneg_left _
      (show 0 ≤ (gaussianK131Amplitude : ℝ) from Rat.cast_nonneg.mpr (by decide +kernel))
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  dsimp only [gammaMainPoly, v, B] at hbd ⊢
  linarith only [hbd]

/-- The explicit reflected-tail bound applies across the whole bridge
to both retained displacements, `1/10` and `9/2`. -/
theorem k131_bridge_aux_bound_le {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {L h : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) (hh : h ≤ 9 / 2) :
    k131AuxReflect α (gaussianBridgeScale L ^ 2) h ≤
      4 * k131AuxReflectBound (gaussianBridgeScale L ^ 2) h := by
  have hy : (100 : ℝ) ≤ gaussianBridgeScale L :=
    (by norm_num only : (100 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have h101 : 101 ≤ gaussianBridgeScale L ^ 2 := by
    nlinarith only [hy, sq_nonneg (gaussianBridgeScale L - 100)]
  have hl : 14 ≤ Real.log (gaussianBridgeScale L ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (k131_radius_log_mem hL).1
  exact
    k131_aux_reflect_bound_le hα hRH h101 (by linarith only [hl]) (by linarith only [hh, hl])
      (by linarith only [hh, hl])

private theorem reflection_weight_nonneg (i : Fin 2) : 0 ≤ reflectionWeights i := by
  fin_cases i
  · change 0 ≤ (973 / 5000 : ℝ) - 1831 / 10000 * Real.exp (-(27 / 16 : ℝ) * (1 / 10))
    have h := Real.exp_le_one_iff.mpr (by norm_num only : -(27 / 16 : ℝ) * (1 / 10) ≤ 0)
    linarith only [h]
  · change 0 ≤ (13 / 1250 : ℝ) - 1 / 80 * Real.exp (-(27 / 16 : ℝ) * (12 / 5))
    have h := Real.add_one_le_exp ((27 / 16 : ℝ) * (12 / 5))
    have he : Real.exp (-(27 / 16 : ℝ) * (12 / 5)) ≤ 1 / 2 := by
      rw [neg_mul, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num only)]
      norm_num only at h ⊢
      linarith only [h]
    linarith only [he]

private theorem reflection_offset_le (i : Fin 2) : reflectionOffsets i ≤ 9 / 2 := by
  fin_cases i
  · change (1 / 10 : ℝ) ≤ 9 / 2
    norm_num only
  · exact le_rfl

private theorem aux_bound_scalar_eq {y : ℝ} (hy : 0 < y) :
    (∑ j : Fin 2, -4 * reflectionWeights j * k131AuxReflectBound (y ^ 2) (reflectionOffsets j)) =
      logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y := by
  unfold logPowerPoly gaussianK131Poly23 gaussianK131PolyHigher
  simp only [Polynomial.eval_finsetSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  let h := reflectionOffsets j
  let v := 2 * Real.log y
  have hv : Real.log (y ^ 2) = v := by rw [Real.log_pow, Nat.cast_ofNat]
  have he :
    Real.exp (-(27 / 16 : ℝ) * (v - h)) =
      Real.exp ((27 / 16 : ℝ) * h) * Real.exp (-(27 / 16 : ℝ) * v) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h23 :
    Real.exp (-(27 / 16 : ℝ) * v) * Real.exp (-(19 / 16 : ℝ) * v) = y ^ (-(23 / 4 : ℝ)) := by
    rw [← Real.exp_add, Real.rpow_def_of_pos hy]
    dsimp only [v]
    congr 1
    ring
  have hp : (y ^ 2) ^ (-(27 / 16 : ℝ)) = Real.exp (-(27 / 16 : ℝ) * v) := by
    rw [Real.rpow_def_of_pos (pow_pos hy 2), hv, mul_comm]
  have h27 : Real.exp (-(27 / 16 : ℝ) * v) * (y ^ 2) ^ (-(27 / 16 : ℝ)) = y ^ (-(27 / 4 : ℝ)) := by
    rw [hp, ← Real.exp_add, Real.rpow_def_of_pos hy]
    dsimp only [v]
    congr 1
    ring
  simp only [k131AuxReflectBound, hv, reflectFactor, reflectPoly, gammaMainPoly,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_add, Polynomial.eval_pow]
  change _ = _
  rw [show reflectionOffsets j = h from rfl, he, ← show 2 * Real.log y = v from rfl]
  rw [← h23, ← h27]
  ring

private theorem aux_bound_scalar_le_pair {α : ℕ → ℝ} (hα : ∀ n, α n ∈ Set.Icc (0 : ℝ) 4)
    (hRH : RiemannHypothesis) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
      ∑ j : Fin 2, -reflectionWeights j * k131AuxReflect α (y ^ 2) (reflectionOffsets j) := by
  intro y
  have hy : 0 < y :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  rw [← aux_bound_scalar_eq hy]
  apply Finset.sum_le_sum
  intro j _
  have h := k131_bridge_aux_bound_le hα hRH hL (reflection_offset_le j)
  have hm := mul_le_mul_of_nonpos_left h (neg_nonpos.mpr (reflection_weight_nonneg j))
  dsimp only [y]
  nlinarith only [hm]

/-- On the K131 bridge the two certified reflection polynomials bound
the weighted reflected contour deficit under RH. -/
theorem k131_gram_reflected_moment_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1)
    (hRH : RiemannHypothesis) (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let X := gaussianBridgeScale L ^ 2
    let x := fun i ↦ X * Real.exp (-(k131GramFreq i))
    logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 (gaussianBridgeScale L) +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher (gaussianBridgeScale L) ≤
      ∑ i : Fin 4,
        k131GramCoeff i *
          ((k131ReflectedIntegral a (x i) + k131ReflectedIntegral b (x i) +
                  k131ReflectedIntegral c (x i)).re -
              (k131ReflectedGamma a (x i) + k131ReflectedGamma b (x i) +
                  k131ReflectedGamma c (x i)).re +
            3 *
              ∑' n : ℕ,
                ArithmeticFunction.vonMangoldt n *
                  (k131MellinProfile (((n : ℝ) * x i)⁻¹) / Real.sqrt n)) := by
  intro X x
  let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hα (n : ℕ) : α n ∈ Set.Icc (0 : ℝ) 4 := by
    dsimp only [α]
    exact
      ⟨by linarith only [(char_gap_mem a n).1, (char_gap_mem b n).1, (char_gap_mem c n).1], by
        linarith only [htrace n]⟩
  have hbound := aux_bound_scalar_le_pair hα hRH hL
  dsimp only at hbound
  have hg := k131_gram_reflected_lower ha hb hc hL ht htrace
  refine hbound.trans ?_
  simpa only [reflectionWeights, reflectionOffsets, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, neg_mul, ← sub_eq_add_neg, α, X, x] using
    hg

/-- On the left line the K131 principal xi and pole terms equal the
reflected Gamma integral minus the unsigned reflected Euler series. -/
theorem k131_left_xi_eq_reflected {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (he : χ.Even)
    (hinv : χ⁻¹ = χ) {x : ℝ} (hx : 0 < x) :
    (k131LeftXiPoles x).re =
      (k131ReflectedGamma χ x).re -
        ∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n *
            (k131MellinProfile (((n : ℝ) * x)⁻¹) / Real.sqrt n) := by
  let s := fun t : ℝ ↦ ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  let w := fun t : ℝ ↦ ((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)
  let W := k131LeftWeight x
  let ζ := (1 : DirichletCharacter ℂ 1)
  let f := (fun n : ℕ ↦ ζ n) * (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ))
  let F := fun t : ℝ ↦ -logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (s t + 1 / 2) * W t
  let P := fun p t : ℝ ↦ (1 / (s t - (p : ℂ))) * W t
  let G := fun t : ℝ ↦ logDeriv χ⁻¹.gammaFactor (w t) * W t
  let E := fun t : ℝ ↦ LSeries f (w t) * W t
  let d : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hs :=
    ζ.LSeriesSummable_twist_vonMangoldt
      (show 1 < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have hW : MeasureTheory.Integrable W := k131_left_weight_int hx
  have hE : MeasureTheory.Integrable E := by
    have h :=
      Analysis.integrable_tsum_of_summable_integral_norm (fun n t ↦ LSeries.term f (w t) n * W t)
        (fun n ↦
          AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
            (fun t : ℝ ↦ -t) continuous_neg W hW)
        (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
          (fun t : ℝ ↦ -t) W)
    exact h.congr (MeasureTheory.ae_of_all _ (fun t ↦ tsum_mul_right))
  have ha : -1 / 2 - k131MellinKernel.delta < (-9 / 16 : ℝ) := by
    rw [k131_kernel_delta]
    norm_num only
  have hb : (-9 / 16 : ℝ) ≤ 1 / 2 + k131MellinKernel.delta := by
    rw [k131_kernel_delta]
    norm_num only
  have hF : MeasureTheory.Integrable F :=
    LLS.PaperStatements.MellinKernel.integrable_xi_left_line k131MellinKernel ha (by norm_num only)
      (by norm_num only) hx
  have hP (p : ℝ) (hp : (-9 / 16 : ℝ) ≠ p) : MeasureTheory.Integrable (P p) := by
    simpa only [P, s, W, k131LeftWeight, mul_assoc,
      show k131MellinKernel.function = k131MellinFn from rfl, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_ofNat] using
      LLS.PaperStatements.MellinKernel.integrable_pole_power_line k131MellinKernel ha hb
        (by norm_num only) hp hx
  have hγ : χ⁻¹.gammaFactor = ζ.gammaFactor := by
    funext z
    rw [hinv, he.gammaFactor_def,
      AnalyticNumberTheory.DirichletLFunction.principal_modulus_one_even.gammaFactor_def]
  have hid (t : ℝ) : G t = F t + P (-1 / 2) t + P (1 / 2) t + E t := by
    have hw : w t = 1 / 2 - s t := by
      dsimp only [w, s]
      push_cast
      ring
    have harg : s t + 1 / 2 = 1 - w t := by
      rw [hw]; ring
    have hp : 1 < (w t).re := by
      dsimp only [w]
      norm_num only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    have hζ : LSeries f (w t) = -logDeriv riemannZeta (w t) := by
      simpa only [f, ζ, DirichletCharacter.LFunction_modOne_eq, Pi.mul_def, logDeriv, Pi.div_apply,
        neg_div] using AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv ζ hp
    dsimp only [G, F, P, E]
    rw [harg, AnalyticNumberTheory.RiemannXi.logDeriv_one_sub,
      AnalyticNumberTheory.RiemannXi.logDeriv_eq_poles_gamma_zeta_of_re_gt_one hp, hγ, hζ]
    have h₁ : w t = -(s t - ((1 / 2 : ℝ) : ℂ)) := by
      rw [hw]; push_cast; ring
    have h₂ : w t - 1 = -(s t - ((-1 / 2 : ℝ) : ℂ)) := by
      rw [hw]; push_cast; ring
    rw [h₁] at h₂
    simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] at h₁ h₂ ⊢
    rw [h₁, h₂]
    simp only [div_neg]
    ring
  have hp := hP (-1 / 2) (by norm_num only)
  have hq := hP (1 / 2) (by norm_num only)
  have hG :
    (∫ t : ℝ, G t) =
      (∫ t : ℝ, F t) + (∫ t : ℝ, P (-1 / 2) t) + (∫ t : ℝ, P (1 / 2) t) + ∫ t : ℝ, E t := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hid)]
    have h₁ := MeasureTheory.integral_add hF hp
    have h₂ := MeasureTheory.integral_add (hF.add hp) hq
    have h₃ := MeasureTheory.integral_add ((hF.add hp).add hq) hE
    simp only [Pi.add_apply] at h₁ h₂ h₃
    rw [h₃, h₂, h₁]
  have hW' := k131_dual_real_sum ζ hx
  simp only [ζ, MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re,
    one_mul] at hW'
  have hdual := congrArg Complex.re (k131_dual_euler_eq hx hs)
  have hEq := congrArg (fun z : ℂ ↦ (d * z).re) hG
  change (d * ∫ t : ℝ, E t).re = _ at hdual
  simp only [ζ, Pi.mul_apply, MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)),
    one_mul] at hdual
  change (k131LeftXiPoles x).re = (d * ∫ t : ℝ, G t).re - _
  have hLeft :
    k131LeftXiPoles x = d * ((∫ t : ℝ, F t) + (∫ t : ℝ, P (-1 / 2) t) + ∫ t : ℝ, P (1 / 2) t) := by
    simp only [k131LeftXiPoles, F, P, d, s, W, k131LeftWeight, Complex.ofReal_neg,
      Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hLeft]
  simp only [mul_add, Complex.add_re] at hEq ⊢
  linarith only [hEq, hdual, hW'.tsum_eq]

/-- Under RH and prime triviality, each shifted K131 contour difference
is its conductor term, the two pole residues, the principal zero sum and
the reflected trace deficit. -/
theorem k131_shifted_deficit_eq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hn : χ ≠ 1) (hi : χ⁻¹ = χ) (he : χ.Even) (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ gaussianBridgeScale L ^ 2 → χ p = 1) (i : Fin 4) :
    let X := gaussianBridgeScale L ^ 2
    let x := X * Real.exp (-(k131GramFreq i))
    k131ShiftedDifference χ L i =
      (Complex.log q * (k131MellinProfile x⁻¹ : ℂ)).re -
          (k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
          (k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re +
        (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm x ρ).re +
        k131AuxReflect (fun n ↦ 1 - (χ n).re) X (k131GramFreq i - 9 / 4) := by
  intro X x
  have hX : 0 < X :=
    pow_pos
      ((by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1)
      2
  have hx : 1 ≤ x := k131_gram_shifted_scale hL i
  have hs : 9 / 4 + (k131GramFreq i - 9 / 4) = k131GramFreq i := by ring
  have haux :=
    k131_aux_reflected_split hp hn hi hX
      (show 1 ≤ X * Real.exp (-(9 / 4 + (k131GramFreq i - 9 / 4))) by
        rw [hs]; exact hx)
      ht
  dsimp only at haux
  rw [hs] at haux
  have hleft := k131_left_xi_eq_reflected χ he hi (zero_lt_one.trans_le hx)
  have hdiff := congrArg Complex.re (k131_xi_poles_difference hRH hx)
  simp only [Complex.sub_re, Complex.add_re] at hdiff
  have hcancel := k131_shifted_principal_cancel χ he hL i
  dsimp only at hcancel
  dsimp only [x, X] at haux hleft hdiff ⊢
  linarith only [haux, hleft, hdiff, hcancel]

/-- The weighted conductor and pole residues of the three shifted K131
contours, expressed in terms of their total logarithmic conductor. -/
@[expose]
noncomputable def k131ShiftPrincipal (C L : ℝ) : ℝ :=
  ∑ i : Fin 4,
    let x := gaussianBridgeScale L ^ 2 * Real.exp (-(k131GramFreq i))
    k131GramCoeff i *
      (C * k131MellinProfile x⁻¹ -
        3 * (k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
        3 * (k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re)

private theorem k131_gram_shift_split {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1) :
    let X := gaussianBridgeScale L ^ 2
    let x := fun i ↦ X * Real.exp (-(k131GramFreq i))
    let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    k131ShiftedGram a L + k131ShiftedGram b L + k131ShiftedGram c L =
      k131ShiftPrincipal (Real.log p + Real.log q + Real.log r) L +
        3 *
          (∑ i : Fin 4,
            k131GramCoeff i * (∑' ρ, k131MellinKernel.zetaOscillatingZeroTerm (x i) ρ).re) +
        ∑ i : Fin 4, k131GramCoeff i * k131AuxReflect α X (k131GramFreq i - 9 / 4) := by
  intro X x α
  simp only [k131ShiftedGram, k131ShiftPrincipal, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have ea :=
    k131_shifted_deficit_eq ha.1 ha.2.1 ha.2.2.1 ha.2.2.2 hRH hL (fun l hl hle ↦ (ht l hl hle).1) i
  have eb :=
    k131_shifted_deficit_eq hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 hRH hL (fun l hl hle ↦ (ht l hl hle).2.1)
      i
  have ec :=
    k131_shifted_deficit_eq hc.1 hc.2.1 hc.2.2.1 hc.2.2.2 hRH hL (fun l hl hle ↦ (ht l hl hle).2.2)
      i
  have es :=
    k131_aux_reflect_add_three (char_gap_mem a) (char_gap_mem b) (char_gap_mem c) X
      (k131GramFreq i - 9 / 4)
  have eα : α = fun n : ℕ ↦ (1 - (a n).re) + (1 - (b n).re) + (1 - (c n).re) := by
    funext n
    dsimp only [α]
    ring
  dsimp only at ea eb ec
  rw [ea, eb, ec, eα, es]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    ← Complex.ofReal_natCast, Complex.log_ofReal_re, X, x]
  ring

/-- Under RH the weighted shifted K131 contour sum is at least its
conductor and pole terms plus the two scalar reflection terms, less the xi allowance. -/
theorem k131_shift_gram_scalar_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ r}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {L : ℝ}
    (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (ht : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ gaussianBridgeScale L ^ 2 → a l = 1 ∧ b l = 1 ∧ c l = 1)
    (htrace : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let y := gaussianBridgeScale L
    k131ShiftPrincipal (Real.log p + Real.log q + Real.log r) L +
          logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
          logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y -
        3 / 5000 ≤
      k131ShiftedGram a L + k131ShiftedGram b L + k131ShiftedGram c L := by
  intro y
  let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hα (n : ℕ) : α n ∈ Set.Icc (0 : ℝ) 4 := by
    dsimp only [α]
    exact
      ⟨by linarith only [(char_gap_mem a n).1, (char_gap_mem b n).1, (char_gap_mem c n).1], by
        linarith only [htrace n]⟩
  have hv : 9 / 2 ≤ Real.log (y ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    exact (by norm_num only : (9 / 2 : ℝ) ≤ 14).trans (k131_radius_log_mem hL).1
  have hm := aux_bound_scalar_le_pair hα hRH hL
  have hg := k131_gram_aux_reflect_lower hα hv
  dsimp only at hm
  have hr :
    logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
        logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
      ∑ i : Fin 4, k131GramCoeff i * k131AuxReflect α (y ^ 2) (k131GramFreq i - 9 / 4) :=
    hm.trans
      (by
        simpa only [reflectionWeights, reflectionOffsets, Fin.sum_univ_succ, Fin.sum_univ_zero,
          Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero, neg_mul, ← sub_eq_add_neg, y] using
          hg)
  have hx := k131_shift_xi_cap hRH hL
  have he := k131_gram_shift_split ha hb hc hRH hL ht
  dsimp only at he hx
  dsimp only [y, α] at hr ⊢
  linarith only [hr, (abs_le.mp hx).1, he]

private theorem k131_mellin_at_pos_half :
    k131MellinFn ((1 / 2 : ℝ) : ℂ) = ((Real.exp (9 / 8) * positivePole : ℝ) : ℂ) := by
  rw [k131_mellin_closed _
      (by norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat])]
  simp only [positivePole, kernelNumerator, k131Numerator, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one, Complex.ofReal_ratCast,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]
  norm_num only
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

private theorem k131_mellin_at_neg_half :
    k131MellinFn ((-1 / 2 : ℝ) : ℂ) = ((Real.exp (-(9 / 8 : ℝ)) * (negativePole : ℝ) : ℝ) : ℂ) := by
  rw [k131_mellin_closed _
      (by
        norm_num only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one,
          Complex.ofReal_ofNat])]
  simp only [negativePole, kernelNumerator, k131Numerator, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one,
    Complex.ofReal_ratCast, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_ofNat]
  norm_num only
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

/-- The weighted conductor and pole residues at physical radius `y`. -/
@[expose]
noncomputable def k131RawShiftPrincipal (C y : ℝ) : ℝ :=
  ∑ i : Fin 4,
    let x := y ^ 2 * Real.exp (-(k131GramFreq i))
    k131GramCoeff i *
      (C * k131MellinProfile x⁻¹ -
        3 * (k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re -
        3 * (k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re)

private theorem k131_shift_residues (i : Fin 4) {y : ℝ} (hy : 0 < y)
    (hscale : 1 ≤ y ^ 2 * Real.exp (-(k131GramFreq i))) :
    let x := y ^ 2 * Real.exp (-(k131GramFreq i))
    (k131MellinFn ((1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((1 / 2 : ℝ) : ℂ)).re =
        positivePole * y * Real.exp (-(offsets i) / 2) ∧
      (k131MellinFn ((-1 / 2 : ℝ) : ℂ) * (x : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re =
        (negativePole : ℝ) * Real.exp (offsets i / 2) / y := by
  intro x
  have hx := zero_lt_one.trans_le hscale
  have hlog : Real.log x = 2 * Real.log y - (9 / 4 + offsets i) := by
    dsimp only [x, k131GramFreq]
    rw [Real.log_mul (pow_pos hy 2).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow,
      Nat.cast_ofNat, sub_eq_add_neg]
  constructor
  · rw [k131_mellin_at_pos_half, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul,
      Complex.ofReal_re, Real.rpow_def_of_pos hx, hlog]
    rw [mul_comm (Real.exp (9 / 8)) positivePole, mul_assoc, ← Real.exp_add]
    have he :
      9 / 8 + (2 * Real.log y - (9 / 4 + offsets i)) * (1 / 2) = Real.log y + -(offsets i) / 2 := by
      ring
    rw [he, Real.exp_add, Real.exp_log hy]
    ring
  · rw [k131_mellin_at_neg_half, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_mul,
      Complex.ofReal_re, Real.rpow_def_of_pos hx, hlog]
    rw [mul_comm (Real.exp (-(9 / 8 : ℝ))) (negativePole : ℝ), mul_assoc, ← Real.exp_add]
    have he :
      -(9 / 8 : ℝ) + (2 * Real.log y - (9 / 4 + offsets i)) * (-1 / 2) =
        -(Real.log y) + offsets i / 2 := by
      ring
    rw [he, Real.exp_add, Real.exp_neg, Real.exp_log hy]
    ring

private theorem k131_shift_profile (i : Fin 4) {y : ℝ} (hy : 0 < y)
    (hscale : 1 ≤ y ^ 2 * Real.exp (-(k131GramFreq i))) :
    let x := y ^ 2 * Real.exp (-(k131GramFreq i))
    k131MellinProfile x⁻¹ =
      (gaussianK131Amplitude : ℝ) * y ^ (-(27 / 8 : ℝ)) * Real.exp ((27 / 16 : ℝ) * offsets i) *
        (shiftPoly gaussianK131InversePoly (-(offsets i))).eval (2 * Real.log y) := by
  intro x
  have h := k131_dual_profile_eq hscale (t := 1) le_rfl
  dsimp only at h
  simp only [one_mul, Real.sqrt_one, div_one, Real.one_rpow, Real.log_one, add_zero] at h
  change k131MellinProfile x⁻¹ = _ at h
  have hz : 9 / 4 + Real.log x = 2 * Real.log y - offsets i := by
    dsimp only [x, k131GramFreq]
    rw [Real.log_mul (pow_pos hy 2).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_pow,
      Nat.cast_ofNat]
    ring
  rw [h, hz, shiftPoly, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C, ← sub_eq_add_neg, gaussian_k131_inverse_eval]
  have he :
    -(27 / 16 : ℝ) * (2 * Real.log y - offsets i) =
      Real.log y * -(27 / 8 : ℝ) + (27 / 16 : ℝ) * offsets i := by
    ring
  rw [he, Real.exp_add, ← Real.rpow_def_of_pos hy]
  ring

/-- Evaluate the conductor and pole terms at a positive radius whose four shifted scales
are at least one. -/
private theorem k131_raw_shift_principal_eval (C : ℝ) {y : ℝ} (hy : 0 < y)
    (hscale : ∀ i, 1 ≤ y ^ 2 * Real.exp (-(k131GramFreq i))) :
    k131RawShiftPrincipal C y =
      -C * (gaussianK131Amplitude : ℝ) * logPowerPoly (-(27 / 8 : ℝ)) shiftedInverse y -
        (3 * positivePole * (∑ j : Fin 4, gram j * Real.exp (-(offsets j) / 2))) * y -
        (3 * (negativePole : ℝ) * (∑ j : Fin 4, gram j * Real.exp (offsets j / 2))) / y := by
  unfold k131RawShiftPrincipal
  simp only [fun i ↦ k131_shift_profile i hy (hscale i),
    fun i ↦ (k131_shift_residues i hy (hscale i)).1,
    fun i ↦ (k131_shift_residues i hy (hscale i)).2, logPowerPoly, shiftedInverse,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_div, ← Finset.sum_sub_distrib, k131GramCoeff]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem k131_shift_principal_eval (C : ℝ) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    k131ShiftPrincipal C L =
      -C * (gaussianK131Amplitude : ℝ) * logPowerPoly (-(27 / 8 : ℝ)) shiftedInverse y -
        (3 * positivePole * (∑ j : Fin 4, gram j * Real.exp (-(offsets j) / 2))) * y -
        (3 * (negativePole : ℝ) * (∑ j : Fin 4, gram j * Real.exp (offsets j / 2))) / y := by
  intro y
  have hy : 0 < y :=
    (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le (gaussian_bridge_scale_mem hL).1
  exact k131_raw_shift_principal_eval C hy (k131_gram_shifted_scale hL)

private theorem k131_reflect_moment_half (z : ℝ) :
    k131ReflectMoment (19 / 32) z / 2 =
      (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval z := by
  let g := fun u : ℝ ↦ Real.exp (-(19 / 16 : ℝ) * u) * gaussianK131Inverse (z + u)
  have h := MeasureTheory.integral_comp_mul_left_Ioi' g 0 (by norm_num only : (0 : ℝ) < 1 / 2)
  have he :
    (fun u : ℝ ↦ g ((1 / 2 : ℝ) * u)) = fun u ↦
      Real.exp (-(19 / 32 : ℝ) * u) * gaussianK131Inverse (z + u / 2) := by
    funext u
    dsimp only [g]
    congr 2 <;> ring
  rw [he, k131_reflect_inverse_moment (by norm_num only : (0 : ℝ) < 19 / 32)] at h
  have hp :=
    k131_shifted_exp_moment (Nat.lt_succ_of_le inverse_degree_le)
      (by norm_num only : (0 : ℝ) < 19 / 16) z 0
  simp only [pow_zero, mul_one, gaussian_k131_inverse_eval] at hp
  simp only [smul_eq_mul, mul_zero] at h
  change _ = ∫ u in Set.Ioi (0 : ℝ), g u at h
  rw [hp] at h
  linarith only [h]

private theorem inverse_moment_zero {r : ℝ} (hr : 0 < r) :
    (k131MomentPoly gaussianK131InversePoly r 0).eval 0 =
      ∑ j : Fin 9,
        (inverseCoeffs j : ℝ) * ((2 * j.val + 3).factorial : ℝ) / r ^ (2 * j.val + 4) := by
  rw [← k131_shifted_exp_moment (Nat.lt_succ_of_le inverse_degree_le) hr]
  simp only [pow_zero, mul_one, zero_add, gaussianK131InversePoly, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, Finset.mul_sum]
  have he (j : Fin 9) (u : ℝ) :
    Real.exp (-r * u) * ((inverseCoeffs j : ℝ) * u ^ (2 * j.val + 3)) =
      (inverseCoeffs j : ℝ) * (u ^ (2 * j.val + 3) * Real.exp (-r * u)) := by
    ring
  simp only [he]
  rw [MeasureTheory.integral_finsetSum _
      (fun j _ ↦ (Analysis.exponential_moment_integrable hr (2 * j.val + 3)).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  rw [MeasureTheory.integral_const_mul, Analysis.exponential_moment_tail hr (le_refl 0), mul_zero,
    Real.exp_zero, one_mul, tail_monomial_moment_zero hr.ne']
  ring

private theorem k131_gamma_zero_eval :
    (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval 0 = (gammaIntegralZero : ℝ) := by
  rw [inverse_moment_zero (by norm_num only : (0 : ℝ) < 19 / 16)]
  simp only [gammaIntegralZero, Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_pow, Rat.cast_ofNat]

private theorem k131_delta_scalar :
    k131PrincipalDelta - 3 * positivePole * (∑ j : Fin 4, gram j * Real.exp (-(offsets j) / 2)) =
      k131Alpha := by
  dsimp only [k131PrincipalDelta]
  rw [inverse_moment_zero (by norm_num only : (0 : ℝ) < 35 / 16)]
  have hq :
    ∑ j : Fin 9,
        inverseCoeffs j * ((2 * j.val + 3).factorial : ℚ) / (35 / 16 : ℚ) ^ (2 * j.val + 4) =
      kernelNumerator (35 / 16) ^ 2 / (35 / 16 : ℚ) ^ 20 := by
    decide +kernel
  have hq' := congrArg (fun t : ℚ ↦ (t : ℝ)) hq
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat] at hq'
  rw [hq']
  have he :
    Real.exp (9 / 8) * Real.exp (-(35 / 16 : ℝ) * (9 / 4)) =
      Real.exp (-(27 / 16 : ℝ) * (9 / 4)) := by
    rw [← Real.exp_add]; congr 1; norm_num only
  simp only [k131Alpha, k131Prefactor, positivePole, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat]
  linear_combination
    (4 * (gaussianK131Amplitude : ℝ) *
        (k131MomentPoly gaussianK131InversePoly (35 / 16) 0).eval (9 / 4)) *
      he

private theorem log_two_pi_lower : reciprocalLogLower ≤ Real.log (2 * Real.pi) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6.283184) (j := 3) (n := 40) (lo := 1.8378765)
        (hi := 1.837878) (by decide +kernel)).1
  have hπ : (392699 / 62500 : ℝ) ≤ 2 * Real.pi := by linarith only [Real.pi_gt_d6]
  norm_num only [Rat.cast_ofScientific] at h
  exact
    (by norm_num only [reciprocalLogLower] : reciprocalLogLower ≤ 3675753 / 2000000).trans
      (h.trans (Real.log_le_log (by norm_num only) hπ))

private theorem log_two_pi_upper :
    (486361785475175632772883470102367621 / 1000000000000000000000000000000000000 : ℝ) ≤
      6 - 3 * Real.log (2 * Real.pi) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6.283186) (j := 3) (n := 40) (lo := 1.8378765)
        (hi := 1.837878) (by decide +kernel)).2
  have hπ : 2 * Real.pi ≤ (3141593 / 500000 : ℝ) := by linarith only [Real.pi_lt_d6]
  norm_num only [Rat.cast_ofScientific] at h
  have hu := (Real.log_le_log (mul_pos (by norm_num only) Real.pi_pos) hπ).trans h
  linarith only [hu]

private theorem k131_gamma_scalar {y : ℝ} (hy : 1 ≤ y) :
    let z := 9 / 4 + Real.log (y ^ 2)
    3 *
        (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
            k131CentralMoment (-(19 / 32 : ℝ)) z /
          2) =
      3 * (gaussianK131Amplitude : ℝ) * Real.exp (-(9 / 8 : ℝ)) * (gammaIntegralZero : ℝ) / y -
        3 * k131Prefactor * y ^ (-(27 / 8 : ℝ)) *
          (k131MomentPoly gaussianK131InversePoly (19 / 16) 0).eval (9 / 4 + 2 * Real.log y) := by
  intro z
  have h := k131_gamma_first_radius hy
  dsimp only at h
  rw [k131Prefactor]
  dsimp only [z]
  rw [Real.log_pow, Nat.cast_ofNat]
  have h₀ := k131_reflect_moment_half 0
  have hz := k131_reflect_moment_half (9 / 4 + 2 * Real.log y)
  rw [k131_gamma_zero_eval] at h₀
  linear_combination
    3 * h + (3 * (gaussianK131Amplitude : ℝ) * Real.exp (-(9 / 8 : ℝ)) / y) * h₀ -
      (3 * (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4)) *
          y ^ (-(27 / 8 : ℝ))) *
        hz

private theorem k131_rem_scalar (y : ℝ) :
    k131PrincipalRem y =
      3 * k131Prefactor * y ^ (-(27 / 8 : ℝ)) * remainderGamma.eval (9 / 4 + 2 * Real.log y) +
        gaussianK131EdgeLoss / y ^ 5 := by
  simp only [k131PrincipalRem, k131Prefactor, remainderGamma, k131RemainderPoly,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  ring

private theorem shifted_pole_sum :
    (∑ j : Fin 4, gram j * Real.exp (offsets j / 2)) =
      1831 / 10000 - 973 / 5000 * Real.exp (1 / 20) + 1 / 80 * Real.exp (21 / 20) -
        13 / 1250 * Real.exp (9 / 4) := by
  simp only [gram, offsets, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero, zero_div, Real.exp_zero, mul_one]
  norm_num only
  ring

/-- The explicit K131 comparison forces the scalar gap below the two
xi allowances on the affine bridge. -/
theorem k131_gap_le_of_comparison {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    (k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
                  4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
                25329 / 1000000 -
                k131PrincipalRem y +
              (2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) -
                (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y) +
              3 *
                (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                    k131CentralMoment (-(19 / 32 : ℝ)) z /
                  2) -
            (2 * L - 6 + 3 * Real.log (2 * Real.pi)) * k131MellinProfile x⁻¹ +
          k131ShiftPrincipal (2 * L) L +
          logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
          logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
        k131PoleConductor (2 * L) 0 + k131GramMix (k131PoleConductor (2 * L)) + 27 / 10000 +
          4 * Real.exp (-(19 / 16 : ℝ) * Real.log x) *
            (k131MomentPoly (gaussianK131Fourier + k131GramEulerPoly) (19 / 16) 0).eval
              (Real.log x) +
          Real.exp (-(27 / 16 : ℝ) * Real.log x) *
              (Real.log x ^ 2 * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log x) +
                (k131MomentPoly
                      (Polynomial.X ^ 2 *
                        (Polynomial.C (35 / 16 : ℝ) * (gaussianK131Fourier + k131GramEulerPoly) -
                          (gaussianK131Fourier + k131GramEulerPoly).derivative))
                      (27 / 16) 0).eval
                  (Real.log x)) /
            6) →
      gaussianK131Gap y ≤ 27 / 10000 := by
  intro y x z hcomp
  have hy : 1 ≤ y :=
    (by norm_num only : (1 : ℝ) ≤ 465644807 / 400000).trans (gaussian_bridge_scale_mem hL).1
  have hyp := zero_lt_one.trans_le hy
  have hg := k131_gamma_scalar hy
  have hs := k131_shift_principal_eval (2 * L) hL
  have hc := k131_core_scalar_eval (2 * L)
  have ht := k131_tail_scalar_eval hyp
  have ha := k131_affine_conductor L
  have hl : L = (y + 123 / 10) / (519674 / 1000000 : ℝ) := by
    dsimp only [y, gaussianBridgeScale]
    ring
  dsimp only at hg hs ht
  dsimp only [x, z] at hcomp
  rw [hg, hs, hc, k131_rem_scalar, shifted_pole_sum, k131_conductor_profile hy, ha, hl] at hcomp
  have hscale : gaussianBridgeScale ((y + 123 / 10) / (519674 / 1000000 : ℝ)) = y :=
    congrArg gaussianBridgeScale hl.symm
  rw [hscale] at hcomp
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hunit : 0 ≤ gaussianK131UnitWeight :=
    mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (k131_inverse_nonneg (by norm_num only))
  have hlower :=
    mul_le_mul_of_nonneg_left log_two_pi_lower
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (div_nonneg hunit hyp.le))
  have hprofile : 0 ≤ k131MellinProfile (y ^ 2)⁻¹ := by
    rw [k131_conductor_profile hy]
    exact
      mul_nonneg (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.rpow_nonneg hyp.le _))
        (k131_inverse_nonneg (by linarith only [Real.log_nonneg hy]))
  have hupper := mul_le_mul_of_nonneg_right log_two_pi_upper hprofile
  rw [k131_conductor_profile hy] at hupper
  have hbudget : 0 ≤ 3 * (2 * gramAbsMass + gramAbsMass ^ 2 / 2) / (100000 : ℝ) := by
    have hn : 0 ≤ gramAbsMass := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    positivity
  have hdelta := congrArg (fun t : ℝ ↦ t * y) k131_delta_scalar
  have hpow5 : y ^ (-(5 : ℝ)) = (y ^ 5)⁻¹ := by
    rw [Real.rpow_neg hyp.le]
    exact congrArg Inv.inv (Real.rpow_natCast y 5)
  have hpow1 : y ^ (-1 : ℝ) = y⁻¹ := Real.rpow_neg_one y
  have hhalf : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg hyp.le, Real.sqrt_eq_rpow]
  simp only [gaussianK131Gap, Fin.sum_univ_succ, Fin.sum_univ_zero, gaussianK131GapExponent,
    gaussianK131GapPoly, Matrix.cons_val_zero, Matrix.cons_val_succ, neg_neg, neg_zero,
    gaussianK131Poly19, gaussianK131Poly27, logPowerPoly, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, hpow5, hpow1, hhalf, Real.rpow_zero, Real.rpow_one,
    add_zero, one_mul, gaussianK131Reciprocal, shiftPoly, Polynomial.eval_comp,
    Polynomial.eval_X] at ⊢
  have hpow : y * y ^ (-(27 / 8 : ℝ)) = y ^ (-(19 / 8 : ℝ)) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (-(27 / 8 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hyp]; norm_num only
  simp only [logPowerPoly, k131Prefactor, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, ← hpow, add_comm (2 * Real.log y) (9 / 4),
    gaussian_k131_inverse_eval] at hcomp ht hupper hlower hdelta ⊢
  ring_nf at hcomp ht hupper hlower hdelta hbudget ⊢
  linarith only [hcomp, ht, hupper, hlower, hbudget, hdelta]

/-- The non-strict scalar comparison forced by prime passes for the raw K131 kernel. -/
def K131RawComparison (n : ℕ) (y : ℝ) : Prop :=
    let x := y ^ 2
    let z := 9 / 4 + Real.log x
    k131PrincipalDelta * y + k131PrincipalError gaussianK131RhCoeff y +
              4 * (gaussianK131UnitWeight / y) * Real.log (2 * Real.pi) -
            25329 / 1000000 -
            k131PrincipalRem y +
          3 *
            (((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * z)) *
                k131CentralMoment (-(19 / 32 : ℝ)) z /
              2) -
        (2 * Real.log n - 6 + 3 * Real.log (2 * Real.pi)) * k131MellinProfile x⁻¹ +
      k131RawShiftPrincipal (2 * Real.log n) y +
      logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
      logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y ≤
    k131PoleConductor (2 * Real.log n) 0 + k131GramMix (k131PoleConductor (2 * Real.log n)) +
      27 / 10000 +
      4 * Real.exp (-(19 / 16 : ℝ) * Real.log x) *
        (k131MomentPoly (gaussianK131Fourier + k131GramEulerPoly) (19 / 16) 0).eval (Real.log x) +
      Real.exp (-(27 / 16 : ℝ) * Real.log x) *
          (Real.log x ^ 2 * (gaussianK131Fourier + k131GramEulerPoly).eval (Real.log x) +
            (k131MomentPoly
                  (Polynomial.X ^ 2 *
                    (Polynomial.C (35 / 16 : ℝ) * (gaussianK131Fourier + k131GramEulerPoly) -
                      (gaussianK131Fourier + k131GramEulerPoly).derivative))
                  (27 / 16) 0).eval
              (Real.log x)) /
        6

/-- A rational affine radius below the old Gaussian envelope from log 8000 onward. -/
noncomputable def gaussianK131TailScale (L : ℝ) : ℝ :=
  (519674 / 1000000 : ℝ) * L - 8

/-- The physical-radius gap with the tail intercept and without square recovery. -/
noncomputable def gaussianK131TailGap (y : ℝ) : ℝ :=
  gaussianK131Gap y + (123 / 10 - 8) * (k131Beta / (2 * (519674 / 1000000))) -
      2 * (gaussianK131Amplitude : ℝ) * gaussianK131Moment (27 / 16) +
    (81 / 100) * gaussianK131RecoveryVariation / Real.sqrt y +
    2 * (123 / 10 - 8) / (519674 / 1000000) *
      logPowerPoly (-(27 / 8 : ℝ))
        (Polynomial.C k131Prefactor * shiftPoly gaussianK131InversePoly (9 / 4) +
          Polynomial.C (gaussianK131Amplitude : ℝ) * shiftedInverse)
        y

/-- Any polynomial in the doubled logarithm multiplied by a strictly
decaying real power tends to zero as the radius increases. -/
theorem k131_power_tendsto_zero {p : ℝ} (hp : 0 < p) (P : Polynomial ℝ) :
    Filter.Tendsto (logPowerPoly (-p) P) Filter.atTop (nhds 0) := by
  let Q := P.comp (Polynomial.C (2 / p) * Polynomial.X)
  have h := Q.tendsto_div_exp_atTop.comp (Real.tendsto_log_atTop.const_mul_atTop hp)
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with y hy
  simp only [Function.comp_apply, Q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, logPowerPoly, Real.rpow_def_of_pos hy, div_eq_mul_inv, ← Real.exp_neg]
  have he : 2 / p * (p * Real.log y) = 2 * Real.log y := by
    rw [← mul_assoc, div_mul_cancel₀ _ hp.ne']
  rw [div_eq_mul_inv] at he
  rw [he, ← neg_mul, mul_comm (Real.log y) (-p), mul_comm (P.eval (2 * Real.log y))]

/-- The two main power-polynomial terms after adjusting the affine intercept. -/
noncomputable def gaussianK131TailMain (y : ℝ) : ℝ :=
  logPowerPoly (-(19 / 8 : ℝ)) gaussianK131Poly19 y +
    logPowerPoly (-(27 / 8 : ℝ)) gaussianK131TailPoly27 y

/-- The two main terms and the two reflected terms of the raw K131 gap. -/
noncomputable def gaussianK131TailVariable (y : ℝ) : ℝ :=
  gaussianK131TailMain y + logPowerPoly (-(23 / 4 : ℝ)) gaussianK131Poly23 y +
    logPowerPoly (-(27 / 4 : ℝ)) gaussianK131PolyHigher y

/-- The four variable polynomial terms and the two constant power terms. -/
noncomputable def gaussianK131TailPowers (y : ℝ) : ℝ :=
  gaussianK131TailVariable y + logPowerPoly (-1 : ℝ) (Polynomial.C gaussianK131Reciprocal) y +
    logPowerPoly (-5 : ℝ) (Polynomial.C (-gaussianK131EdgeLoss)) y

/-- The two constant power terms contribute at least three thousandths
throughout the radius range of the raw K131 interval. -/
theorem k131_tail_powers_lower {y : ℝ} (ha : 4000 ≤ y) (hb : y ≤ 22032) :
    gaussianK131TailVariable y + 3 / 1000 ≤ gaussianK131TailPowers y := by
  have hy : 0 < y := (by norm_num only : (0 : ℝ) < 4000).trans_le ha
  have hp := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 4000) ha 5
  have hr : (76 / 22032 : ℝ) ≤ gaussianK131Reciprocal / y := by
    have hc : (76 : ℝ) ≤ gaussianK131Reciprocal :=
      (by norm_num only : (76 : ℝ) ≤ 7603577 / 100000).trans endpoint_reciprocal_lower
    exact
      (div_le_div_of_nonneg_left (by norm_num only) hy hb).trans
        (div_le_div_of_nonneg_right hc hy.le)
  have he : gaussianK131EdgeLoss / y ^ 5 ≤ 1 / 1000000 := by
    rw [div_le_iff₀ (pow_pos hy 5)]
    linarith only [hp, endpoint_edge_loss_upper]
  have hpow : y ^ (-5 : ℝ) = (y ^ (5 : ℕ))⁻¹ := by
    rw [Real.rpow_neg hy.le]
    exact congrArg Inv.inv (Real.rpow_natCast y 5)
  simp only [gaussianK131TailPowers, logPowerPoly, Polynomial.eval_C, Real.rpow_neg_one, hpow]
  rw [mul_comm y⁻¹, mul_comm (y ^ (5 : ℕ))⁻¹, ← div_eq_mul_inv, ← div_eq_mul_inv, neg_div]
  linarith only [hr, he]

/-- The physical-radius terms remaining after removal of the affine part. -/
noncomputable def gaussianK131TailRemainder (y : ℝ) : ℝ :=
  gaussianK131TailPowers y + k131PrincipalError gaussianK131RhCoeff y

/-- The raw K131 gap is the six decaying terms and the principal RH error,
together with a leading affine contribution. -/
private theorem k131_tail_gap_split {y : ℝ} (hy : 0 ≤ y) :
    gaussianK131TailGap y =
      gaussianK131TailRemainder y + (k131Alpha - k131Beta / (2 * (519674 / 1000000))) * y +
        (6 * halfLineMass - 3 / 100000 - 25329 / 1000000 + reflectedConstant -
          k131Beta * 8 / (2 * (519674 / 1000000))) := by
  have hs : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by rw [Real.rpow_neg hy, Real.sqrt_eq_rpow]
  simp only [gaussianK131TailGap, gaussianK131TailRemainder, gaussianK131TailPowers,
    gaussianK131TailVariable, gaussianK131TailMain, gaussianK131Gap, gaussianK131TailPoly27,
    tailInterceptDelta, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Fin.sum_univ_succ,
    Fin.sum_univ_zero, gaussianK131GapExponent, gaussianK131GapPoly, Matrix.cons_val_zero,
    Matrix.cons_val_succ, neg_neg, neg_zero, logPowerPoly, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_mul, Real.rpow_zero, Real.rpow_one, add_zero, one_mul, hs]
  ring

/-- A rational affine lower bound leaves only the six radius terms and the
principal RH error to be bounded in the raw K131 gap. -/
theorem k131_tail_gap_affine_lower {y : ℝ} (hy : 0 ≤ y) :
    12020425 / 1000000 - 228016 / 1000000000 * y + gaussianK131TailRemainder y ≤
      gaussianK131TailGap y := by
  have hh : (2.62804849 : ℝ) ≤ halfLineMass := by
    change _ ≤ (halfLineRat : ℝ)
    dyadic_interval [prec := 66]
  have ha := alpha_lower
  have hb := beta_upper
  have hr := reflected_lower
  rw [show (2.62804849 : ℝ) = 262804849 / 100000000 by norm_num only] at hh
  rw [show (0.72086441 : ℝ) = 72086441 / 100000000 by norm_num only] at ha
  rw [show (0.74946597 : ℝ) = 74946597 / 100000000 by norm_num only] at hb
  rw [show (2.04623332 : ℝ) = 204623332 / 100000000 by norm_num only] at hr
  have hs : -(228016 / 1000000000 : ℝ) ≤ k131Alpha - k131Beta / (2 * (519674 / 1000000)) := by
    ring_nf
    linarith only [ha, hb]
  have hc :
    (12020425 / 1000000 : ℝ) ≤
      6 * halfLineMass - 3 / 100000 - 25329 / 1000000 + reflectedConstant -
        k131Beta * 8 / (2 * (519674 / 1000000)) := by
    ring_nf
    linarith only [hh, hr, hb]
  rw [k131_tail_gap_split hy]
  have hm := mul_le_mul_of_nonneg_right hs hy
  linarith only [hm, hc]

/-- A raw comparison at the tail scale forces the adjusted scalar gap below the
common allowance for the zeta zero sums. -/
theorem k131_tail_gap_le_of_comparison {n : ℕ} (hL : 8000 ≤ Real.log n)
    (hcomp : K131RawComparison n (gaussianK131TailScale (Real.log n))) :
    gaussianK131TailGap (gaussianK131TailScale (Real.log n)) ≤ 27 / 10000 := by
  let L := Real.log n
  let y := gaussianK131TailScale L
  change K131RawComparison n y at hcomp
  change gaussianK131TailGap y ≤ _
  have hy : 1 ≤ y := by
    dsimp only [y, L, gaussianK131TailScale]
    linarith only [hL]
  have hv : 14 ≤ 2 * Real.log y := by
    have h4 : 4000 ≤ y := by
      dsimp only [y, L, gaussianK131TailScale]; linarith only [hL]
    have hlo :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 4000 12 12 8 9 = true by decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hlo
    have hlog := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 4000) h4)
    linarith only [hlog]
  have hscl (i : Fin 4) : 1 ≤ y ^ 2 * Real.exp (-(k131GramFreq i)) := by
    have hf := (k131_gram_freq_mem i).2
    have he : Real.exp (k131GramFreq i) ≤ y ^ 2 := by
      rw [← Real.exp_log (pow_pos (zero_lt_one.trans_le hy) 2), Real.log_pow, Nat.cast_ofNat]
      exact Real.exp_le_exp.mpr (by linarith only [hf, hv])
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
    exact he
  dsimp only [K131RawComparison] at hcomp
  have hyp := zero_lt_one.trans_le hy
  have hg := k131_gamma_scalar hy
  have hs := k131_raw_shift_principal_eval (2 * L) hyp hscl
  have hc := k131_core_scalar_eval (2 * L)
  have ht := k131_tail_scalar_eval hyp
  have ha : 2 * L * k131Beta / 4 = (y + 8) * (k131Beta / (2 * (519674 / 1000000))) := by
    dsimp only [y, gaussianK131TailScale]
    ring
  have hl : L = (y + 8) / (519674 / 1000000 : ℝ) := by
    dsimp only [y, gaussianK131TailScale]
    ring
  dsimp only at hg hs ht
  rw [hg, hs, hc, k131_rem_scalar, shifted_pole_sum, k131_conductor_profile hy, ha, hl] at hcomp
  rw [show Real.log n = (y + 8) / (519674 / 1000000 : ℝ) from hl] at hcomp
  have hA : 0 ≤ (gaussianK131Amplitude : ℝ) := Rat.cast_nonneg.mpr (by decide +kernel)
  have hunit : 0 ≤ gaussianK131UnitWeight :=
    mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (k131_inverse_nonneg (by norm_num only))
  have hlower :=
    mul_le_mul_of_nonneg_left log_two_pi_lower
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (div_nonneg hunit hyp.le))
  have hprofile : 0 ≤ k131MellinProfile (y ^ 2)⁻¹ := by
    rw [k131_conductor_profile hy]
    exact
      mul_nonneg (mul_nonneg (mul_nonneg hA (Real.exp_pos _).le) (Real.rpow_nonneg hyp.le _))
        (k131_inverse_nonneg (by linarith only [Real.log_nonneg hy]))
  have hupper := mul_le_mul_of_nonneg_right log_two_pi_upper hprofile
  rw [k131_conductor_profile hy] at hupper
  have hbudget : 0 ≤ 3 * (2 * gramAbsMass + gramAbsMass ^ 2 / 2) / (100000 : ℝ) := by
    have hn : 0 ≤ gramAbsMass := Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
    positivity
  have hdelta := congrArg (fun t : ℝ ↦ t * y) k131_delta_scalar
  have hpow5 : y ^ (-(5 : ℝ)) = (y ^ 5)⁻¹ := by
    rw [Real.rpow_neg hyp.le]
    exact congrArg Inv.inv (Real.rpow_natCast y 5)
  have hpow1 : y ^ (-1 : ℝ) = y⁻¹ := Real.rpow_neg_one y
  have hhalf : y ^ (-(1 / 2 : ℝ)) = (Real.sqrt y)⁻¹ := by
    rw [Real.rpow_neg hyp.le, Real.sqrt_eq_rpow]
  simp only [gaussianK131TailGap, gaussianK131Gap, Fin.sum_univ_succ, Fin.sum_univ_zero,
    gaussianK131GapExponent, gaussianK131GapPoly, Matrix.cons_val_zero, Matrix.cons_val_succ,
    neg_neg, neg_zero, gaussianK131Poly19, gaussianK131Poly27, logPowerPoly, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, hpow5, hpow1, hhalf,
    Real.rpow_zero, Real.rpow_one, add_zero, one_mul, gaussianK131Reciprocal, shiftPoly,
    Polynomial.eval_comp, Polynomial.eval_X] at ⊢
  have hpow : y * y ^ (-(27 / 8 : ℝ)) = y ^ (-(19 / 8 : ℝ)) := by
    calc
      _ = y ^ (1 : ℝ) * y ^ (-(27 / 8 : ℝ)) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hyp]; norm_num only
  simp only [logPowerPoly, k131Prefactor, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, ← hpow, add_comm (2 * Real.log y) (9 / 4),
    gaussian_k131_inverse_eval] at hcomp ht hupper hlower hdelta ⊢
  ring_nf at hcomp ht hupper hlower hdelta hbudget ⊢
  linarith only [hcomp, ht, hupper, hlower, hbudget, hdelta]

end PseudoPrime.PrimeTestBounds.MillerRabin
