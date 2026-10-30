/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletError
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
/-! # Logarithmic zeta as the full psi Abel integral -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic
/-- For real exponent and argument above one, differentiate `1/(t^s log t)`.
Normalize the real powers and the nonzero logarithmic denominator explicitly. -/
theorem inv_rpow_log_hasDerivAt {s t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t : ℝ ↦ 1 / (t ^ s * Real.log t))
      (-((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))) t := by
  have ht0 := zero_lt_one.trans ht
  have hl0 := Real.log_pos ht
  have h := (hasDerivAt_const t (1 : ℝ)).div
    ((Real.hasDerivAt_rpow_const (p := s) (Or.inl ht0.ne')).mul
      (Real.hasDerivAt_log ht0.ne'))
    (mul_ne_zero (Real.rpow_pos_of_pos ht0 s).ne' hl0.ne')
  convert h using 1
  dsimp only [Pi.mul_apply]
  have hp : t ^ (s + 1) = t ^ s * t := by
    rw [Real.rpow_add ht0, Real.rpow_one]
  have hm : t ^ (s - 1) = t ^ s / t := by
    rw [Real.rpow_sub ht0, Real.rpow_one]
  rw [hp, hm]
  field_simp (disch := first | exact ht0.ne' | exact hl0.ne' |
    exact (Real.rpow_pos_of_pos ht0 s).ne')
  ring

/-- For every nonnegative real argument, psi is at most six times the argument.
Use the existing Chebyshev estimate and the elementary bound `log 4 ≤ 2`. -/
theorem psi_le_six_mul {t : ℝ} (ht : 0 ≤ t) : Chebyshev.psi t ≤ 6 * t := by
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 2)
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num only, Real.log_pow]
    norm_num only at h ⊢
    linarith only [h]
  have h := Chebyshev.psi_le_const_mul_self ht
  nlinarith only [h, mul_le_mul_of_nonneg_right hlog4 ht]

/-- Above two and for exponent greater than one, the psi Dirichlet kernel is bounded
by `6(2s+4)t^(-s)`. The Chebyshev bound and `log t ≥ 1/2` provide an integrable majorant. -/
theorem psiLogDirichletKernel_norm_le {s t : ℝ} (hs : 1 < s) (ht : 2 < t) :
    ‖Chebyshev.psi t * ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))‖ ≤
      (6 * (2 * s + 4)) * t ^ (-s) := by
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans ht
  have hl0 : 0 < Real.log t := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans ht)
  have hs0 : 0 < s := zero_lt_one.trans hs
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) ht.le
    linarith only [h, Real.log_two_gt_d9]
  have hloglin : Real.log t ≤ 2 * (Real.log t) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right hlhalf hl0.le]
  have hlogsq : 1 ≤ 4 * (Real.log t) ^ 2 := by
    nlinarith only [mul_self_le_mul_self (by norm_num only : (0 : ℝ) ≤ 1 / 2) hlhalf]
  have hn : s * Real.log t + 1 ≤ (2 * s + 4) * (Real.log t) ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_left hloglin hs0.le, hlogsq]
  have hD : (s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2) ≤
      (2 * s + 4) / t ^ (s + 1) := by
    calc
      _ ≤ ((2 * s + 4) * (Real.log t) ^ 2) /
          (t ^ (s + 1) * (Real.log t) ^ 2) :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = _ := by field_simp (disch := exact hl0.ne')
  have hD0 : 0 ≤ (s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Chebyshev.psi_nonneg t) hD0)]
  calc
    _ ≤ (6 * t) * ((s * Real.log t + 1) /
        (t ^ (s + 1) * (Real.log t) ^ 2)) :=
      mul_le_mul_of_nonneg_right (psi_le_six_mul ht0.le) hD0
    _ ≤ (6 * t) * ((2 * s + 4) / t ^ (s + 1)) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by
      rw [Real.rpow_add ht0, Real.rpow_one,
        show -s = -(s) by rfl, Real.rpow_neg ht0.le]
      field_simp (disch := exact ht0.ne')

/-- For exponent greater than one, the full psi Dirichlet kernel is integrable above two.
Dominate the measurable kernel by the established integrable power bound. -/
theorem integrable_psiLogDirichletKernel {s : ℝ} (hs : 1 < s) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ ↦ Chebyshev.psi t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))) (Set.Ioi 2) := by
  have hi := (integrableOn_Ioi_rpow_of_lt (by linarith only [hs] : -s < -1)
    (by norm_num only : (0 : ℝ) < 2)).const_mul (6 * (2 * s + 4))
  have hm : Measurable
      (fun t : ℝ ↦ Chebyshev.psi t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))) :=
    Chebyshev.psi_mono.measurable.mul
      (((measurable_const.mul Real.measurable_log).add measurable_const).div
        ((measurable_id.pow_const (s + 1)).mul (Real.measurable_log.pow_const 2)))
  apply MeasureTheory.Integrable.mono' hi hm.aestronglyMeasurable
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact psiLogDirichletKernel_norm_le hs ht


/-- For argument at least two and any real exponent, the Abel boundary contribution
is at most `12t^(1-s)`, using the Chebyshev estimate and `log t ≥ 1/2`. -/
theorem psiLogDirichlet_boundary_le {s t : ℝ} (ht : 2 ≤ t) :
    Chebyshev.psi t / (t ^ s * Real.log t) ≤ 12 * t ^ (1 - s) := by
  have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht
  have hl0 : 0 < Real.log t := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans_le ht)
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 2) ht
    linarith only [h, Real.log_two_gt_d9]
  have hinv : 1 / Real.log t ≤ (2 : ℝ) := (div_le_iff₀ hl0).mpr
    (by linarith only [hlhalf])
  have hp : 0 < t ^ s := Real.rpow_pos_of_pos ht0 s
  calc
    _ = (Chebyshev.psi t / t ^ s) * (1 / Real.log t) := by ring
    _ ≤ ((6 * t) / t ^ s) * 2 :=
      mul_le_mul (div_le_div_of_nonneg_right (psi_le_six_mul ht0.le) hp.le) hinv
        (div_nonneg (by norm_num only) hl0.le) (by positivity)
    _ = _ := by
      rw [Real.rpow_sub ht0, Real.rpow_one]
      ring

/-- For exponent greater than one, the psi Abel boundary term tends to zero.
Squeeze it by the decaying real power from the explicit boundary estimate. -/
theorem tendsto_psiLogDirichlet_boundary {s : ℝ} (hs : 1 < s) :
    Filter.Tendsto (fun t : ℝ ↦ Chebyshev.psi t / (t ^ s * Real.log t))
      Filter.atTop (nhds 0) := by
  have hp := (tendsto_rpow_neg_atTop (sub_pos.mpr hs)).const_mul 12
  simp only [mul_zero] at hp
  rw [show -(s - 1) = 1 - s by ring] at hp
  apply squeeze_zero' ?_ ?_ hp
  · filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with t ht
    exact div_nonneg (Chebyshev.psi_nonneg t)
      (mul_nonneg (Real.rpow_nonneg (by linarith only [ht] : (0 : ℝ) ≤ t) _)
        (Real.log_nonneg (by linarith only [ht] : (1 : ℝ) ≤ t)))
  · exact (Filter.eventually_ge_atTop (2 : ℝ)).mono
      (fun t ht ↦ psiLogDirichlet_boundary_le (s := s) ht)

/-- For cutoff at least two and any real exponent, the finite logarithmic Mangoldt
Dirichlet sum equals its psi boundary term plus the exact differentiated-weight integral.
Apply finite Abel summation on `[2,x]`, preserving the zero and one coefficients. -/
theorem mangoldtLogDirichlet_finite_abel {s x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s * Real.log n)) =
      Chebyshev.psi x / (x ^ s * Real.log x) +
        ∫ t : ℝ in (2 : ℝ)..x, Chebyshev.psi t *
          ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2)) := by
  let f : ℝ → ℝ := fun t ↦ 1 / (t ^ s * Real.log t)
  have hdiff : ∀ t ∈ Set.Icc 2 x, DifferentiableAt ℝ f t :=
    fun t ht ↦ (inv_rpow_log_hasDerivAt
      ((by norm_num only : (1 : ℝ) < 2).trans_le ht.1)).differentiableAt
  have hc : ContinuousOn
      (fun t : ℝ ↦ -((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2)))
      (Set.Icc 2 x) := by
    intro t ht
    have ht0 : 0 < t := (by norm_num only : (0 : ℝ) < 2).trans_le ht.1
    have hlog := Real.continuousAt_log ht0.ne'
    have hpow : ContinuousAt (fun t : ℝ ↦ t ^ (s + 1)) t :=
      continuousAt_id.rpow_const (Or.inl ht0.ne')
    exact ((((continuousAt_const.mul hlog).add continuousAt_const).div
      (hpow.mul (hlog.pow 2)) (by
        have hl := Real.log_pos ((by norm_num only : (1 : ℝ) < 2).trans_le ht.1)
        change t ^ (s + 1) * (Real.log t) ^ 2 ≠ 0
        exact mul_ne_zero (Real.rpow_pos_of_pos ht0 _).ne'
          (pow_ne_zero 2 hl.ne'))).neg).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 2 x) :=
    hc.integrableOn_Icc.congr_fun
      (fun t ht ↦ (inv_rpow_log_hasDerivAt
        ((by norm_num only : (1 : ℝ) < 2).trans_le ht.1)).deriv.symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ (fun n ↦ ArithmeticFunction.vonMangoldt n)
    ArithmeticFunction.map_zero ArithmeticFunction.vonMangoldt_apply_one x hdiff hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  have he : (∫ t : ℝ in Set.Ioc 2 x, deriv f t * Chebyshev.psi t) =
      -(∫ t : ℝ in Set.Ioc 2 x, Chebyshev.psi t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2))) := by
    rw [← MeasureTheory.integral_neg]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(inv_rpow_log_hasDerivAt ((by norm_num only : (1 : ℝ) < 2).trans ht.1)).deriv]
    ring
  rw [he] at h
  have hsum : (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, f n * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s * Real.log n) := by
    rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
    simp only [ArithmeticFunction.map_zero, mul_zero, add_zero]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [f]
    ring
  rw [hsum] at h
  rw [intervalIntegral.integral_of_le hx]
  dsimp only [f] at h
  rw [h]
  ring


/-- For exponent greater than one, the logarithmic Mangoldt Dirichlet series converges
absolutely. Compare its nonnegative terms with the convergent real p-series. -/
theorem summable_mangoldtLogDirichlet {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ s * Real.log n)) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Real.log_natCast_nonneg n))) ?_
    (Real.summable_one_div_nat_rpow.mpr hs)
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, zero_div]
    exact div_nonneg (by norm_num only) (Real.rpow_nonneg (by norm_num only) _)
  · by_cases hn1 : n = 1
    · subst n
      simp only [ArithmeticFunction.vonMangoldt_apply_one, zero_div]
      exact div_nonneg (by norm_num only) (Real.rpow_nonneg (by norm_num only) _)
    · have hn2 : 1 < n := Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hn0) (Ne.symm hn1)
      have hnR : (1 : ℝ) < n := Nat.one_lt_cast.mpr hn2
      have hnR0 : 0 < (n : ℝ) := zero_lt_one.trans hnR
      have hp := Real.rpow_pos_of_pos hnR0 s
      have hl := Real.log_pos hnR
      apply (div_le_div_iff₀ (mul_pos hp hl) hp).mpr
      nlinarith only [mul_le_mul_of_nonneg_right
        (ArithmeticFunction.vonMangoldt_le_log (n := n)) hp.le]

/-- For exponent greater than one, finite logarithmic Mangoldt sums converge to
logarithmic zeta. Combine the convergent series with the real logarithmic Euler identity. -/
theorem tendsto_mangoldtLogDirichlet_sum {s : ℝ} (hs : 1 < s) :
    Filter.Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s * Real.log n))
      Filter.atTop (nhds (Real.log (riemannZeta (s : ℂ)).re)) := by
  have ht := (summable_mangoldtLogDirichlet hs).hasSum.tendsto_sum_nat.comp
    (Filter.tendsto_add_atTop_nat 1)
  rw [← log_riemannZeta_eq hs] at ht
  apply Filter.Tendsto.congr' ?_ ht
  exact Filter.Eventually.of_forall (fun N ↦ by
    have he : Finset.Icc 0 N = Finset.range (N + 1) := by
      ext n
      simp only [Finset.mem_Icc, Nat.zero_le, true_and, Finset.mem_range, Nat.lt_succ_iff]
    change (∑ n ∈ Finset.range (N + 1),
      ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s * Real.log n)) =
      ∑ n ∈ Finset.Ioc 0 N, ArithmeticFunction.vonMangoldt n /
        ((n : ℝ) ^ s * Real.log n)
    rw [← he, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N)]
    simp only [ArithmeticFunction.map_zero, zero_div, add_zero])

/-- For real exponent greater than one, logarithmic zeta equals the full psi kernel
integral above two. Pass finite Abel summation to infinity, using the vanishing boundary,
convergent series and integrable differentiated-weight kernel. -/
theorem logZeta_eq_psiLogDirichlet_integral {s : ℝ} (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re =
      ∫ t : ℝ in Set.Ioi 2, Chebyshev.psi t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2)) := by
  have hi := integrable_psiLogDirichletKernel hs
  have hI := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 2 hi
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hB := (tendsto_psiLogDirichlet_boundary hs).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have ht := hB.add hI
  simp only [zero_add] at ht
  have hsum : Filter.Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc 0 N,
        ArithmeticFunction.vonMangoldt n / ((n : ℝ) ^ s * Real.log n))
      Filter.atTop (nhds (∫ t : ℝ in Set.Ioi 2, Chebyshev.psi t *
        ((s * Real.log t + 1) / (t ^ (s + 1) * (Real.log t) ^ 2)))) := by
    apply Filter.Tendsto.congr' ?_ ht
    filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with N hN
    have hNR : (2 : ℝ) ≤ N := Nat.ofNat_le_cast.mpr hN
    have h := mangoldtLogDirichlet_finite_abel (s := s) hNR
    rw [Nat.floor_natCast] at h
    exact h.symm
  exact tendsto_nhds_unique (tendsto_mangoldtLogDirichlet_sum hs) hsum


end PseudoPrime.AnalyticNumberTheory.Arithmetic
