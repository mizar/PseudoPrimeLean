/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler

/-! # Shifted reflected Mangoldt tail in the two-frequency phase estimate -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Density of the reflected Mangoldt tail in (96.22), before its scalar prefactor.
At shift z = log X − 1/5 its polynomial is (log t + z)^5. -/
@[expose]
noncomputable def twoShiftReflectedDensity (z t : ℝ) : ℝ :=
  t ^ (-(38 / 25 : ℝ)) * (Real.log t + z) ^ 5

/-- The negative slope contains the degree-five polynomial in the error integral of (96.22). -/
theorem twoShiftReflected_deriv (z : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (twoShiftReflectedDensity z)
      (-(t ^ (-(38 / 25 : ℝ) - 1) * ((38 / 25) * (Real.log t + z) ^ 5 - 5 * (Real.log t + z) ^ 4)))
      t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := -(38 / 25 : ℝ)) (Or.inl ht.ne')).mul
      (((Real.hasDerivAt_log ht.ne').add_const z).pow 5)
  apply h.congr_deriv
  rw [Real.rpow_sub ht, Real.rpow_one]
  simp only [Pi.pow_apply, div_eq_mul_inv]
  ring

private theorem reflected_slope_continuous (z : ℝ) {t : ℝ} (hp : 0 < t) :
    ContinuousAt (deriv (twoShiftReflectedDensity z)) t := by
  let F := fun v : ℝ ↦
    -(v ^ (-(38 / 25 : ℝ) - 1) * ((38 / 25) * (Real.log v + z) ^ 5 - 5 * (Real.log v + z) ^ 4))
  have hF : ContinuousAt F t := by
    dsimp only [F]
    have hlog := (Real.continuousAt_log hp.ne').add_const z
    exact
      ((Real.continuousAt_rpow_const t _ (Or.inl hp.ne')).mul
          (((hlog.pow 5).const_mul (38 / 25 : ℝ)).sub ((hlog.pow 4).const_mul 5))).neg
  apply hF.congr
  apply Filter.eventuallyEq_of_mem (Ioi_mem_nhds hp)
  intro v hv
  exact (twoShiftReflected_deriv z hv).deriv.symm

/-- Finite centered Abel summation for the shifted reflected density. Both boundary
terms retain their signs before the RH estimate is applied. -/
theorem twoShiftReflected_abel (z : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n) -
        (∫ t : ℝ in a..b, twoShiftReflectedDensity z t) =
      (Chebyshev.psi b - b) * twoShiftReflectedDensity z b -
        (Chebyshev.psi a - a) * twoShiftReflectedDensity z a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv (twoShiftReflectedDensity z) t := by
  apply AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
  · exact fun t ht ↦ (twoShiftReflected_deriv z (ha.trans_le ht.1)).differentiableAt
  · apply ContinuousOn.integrableOn_Icc
    exact fun t ht ↦ (reflected_slope_continuous z (ha.trans_le ht.1)).continuousWithinAt

/-- Under RH the finite centered Abel error is bounded by the square-root
log-square envelope times the explicit negative slope in (96.22). -/
theorem twoShiftReflected_error_RH (hRH : RiemannHypothesis) {a b z : ℝ} (ha : 101 ≤ a)
    (hab : a ≤ b) (hz : 5 ≤ Real.log a + z) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv (twoShiftReflectedDensity z) t| ≤
      ∫ t : ℝ in a..b,
        Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t := by
  have ha0 : 0 < a := by linarith only [ha]
  have hcont :
    ContinuousOn
      (fun t : ℝ ↦ Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t)
      (Set.Icc a b) := by
    intro t ht
    have hp := ha0.trans_le ht.1
    exact
      ((Real.continuous_sqrt.continuousAt.mul
              (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).mul
          (reflected_slope_continuous z hp).neg).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have hp := ha0.trans ht.1
  have hv := hz.trans (add_le_add_left (Real.log_le_log ha0 ht.1.le) z)
  have hn : deriv (twoShiftReflectedDensity z) t ≤ 0 := by
    rw [(twoShiftReflected_deriv z hp).deriv, neg_nonpos]
    apply mul_nonneg (Real.rpow_nonneg hp.le _)
    rw [pow_succ (Real.log t + z) 4]
    nlinarith only [mul_nonneg (pow_nonneg (show 0 ≤ Real.log t + z by linarith only [hv]) 4)
        (show 0 ≤ 38 / 25 * (Real.log t + z) - 5 by linarith only [hv])]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
  exact mul_le_mul_of_nonneg_right (psi_log_sq_of_RH hRH (ha.trans ht.1.le)) (neg_nonneg.mpr hn)

/-- The finite reflected Mangoldt sum is bounded by the main integral, the two
centered boundary terms and the RH slope error. This is the finite form of (96.22). -/
theorem twoShiftReflected_sum_upper (hRH : RiemannHypothesis) {a b z : ℝ} (ha : 101 ≤ a)
    (hab : a ≤ b) (hz : 5 ≤ Real.log a + z) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n) ≤
      (∫ t : ℝ in a..b, twoShiftReflectedDensity z t) +
            (Chebyshev.psi b - b) * twoShiftReflectedDensity z b -
          (Chebyshev.psi a - a) * twoShiftReflectedDensity z a +
        ∫ t : ℝ in a..b,
          Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t := by
  have he := (abs_le.mp (twoShiftReflected_error_RH hRH ha hab hz)).1
  linarith only [he, twoShiftReflected_abel z (show 0 < a by linarith only [ha]) hab]

/-- The upper centered boundary vanishes for every fixed shift. Expand the fifth
power and use the decay of each of the six logarithmic moments. -/
theorem twoShiftReflected_boundary (z : ℝ) :
    Filter.Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) * twoShiftReflectedDensity z x) Filter.atTop
      (nhds 0) := by
  let E := fun x : ℝ ↦ (Chebyshev.psi x - x) / 4
  have hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 := zero_le_one.trans hx
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hu :=
      (Chebyshev.psi_le_const_mul_self hx0).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) hx0)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    constructor <;> linarith only [hu, Chebyshev.psi_nonneg (x := x), hx0]
  have hm (k : ℕ) :=
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 38 / 25)
      k E hE
  have hh :=
    tendsto_finsetSum (Finset.range 6)
      (fun k _ ↦ (hm k).const_mul (4 * (Nat.choose 5 k : ℝ) * z ^ (5 - k)))
  simp only [mul_zero, Finset.sum_const_zero] at hh
  apply hh.congr
  intro x
  dsimp only [twoShiftReflectedDensity, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, E]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
  ring

/-- Absolute convergence of the shifted Mangoldt series follows from the six
logarithmic Dirichlet series at exponent 38/25. -/
theorem twoShiftReflected_summable (z : ℝ) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only)
  have hs :=
    summable_sum (s := Finset.range 6)
      (fun k _ ↦ (hm k).mul_left ((Nat.choose 5 k : ℝ) * z ^ (5 - k)))
  apply hs.congr
  intro n
  unfold twoShiftReflectedDensity
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, div_eq_mul_inv]
  ring

/-- Eventual bounds on the main and RH error integrals bound the full reflected tail.
The centered upper boundary vanishes as the upper endpoint tends to infinity. -/
theorem twoShiftReflected_tail_upper (hRH : RiemannHypothesis) {a z M D : ℝ} (ha : 101 ≤ a)
    (hz : 5 ≤ Real.log a + z)
    (hm : ∀ᶠ b : ℝ in Filter.atTop, (∫ t : ℝ in a..b, twoShiftReflectedDensity z t) ≤ M)
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b,
            Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t) ≤
          D) :
    let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      M - (Chebyshev.psi a - a) * twoShiftReflectedDensity z a + D := by
  intro f
  have hf : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_mul]
  have hn :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix f hf (twoShiftReflected_summable z) a
  have ht :=
    hn.comp
      (show Filter.Tendsto (fun b : ℝ ↦ ⌊b⌋₊) Filter.atTop Filter.atTop from
        tendsto_nat_floor_atTop)
  have h := ht.sub (twoShiftReflected_boundary z)
  rw [sub_zero] at h
  apply le_of_tendsto h
  filter_upwards [hm, hd, Filter.eventually_ge_atTop a] with b hb he hab
  dsimp only [Function.comp_apply, f]
  linarith only [twoShiftReflected_sum_upper hRH ha hab hz, hb, he]

/-- The main reflected integral is bounded by its six closed logarithmic moments
at the lower endpoint. Nonnegativity of the shift permits dropping the upper endpoint. -/
theorem twoShiftReflected_main_upper {a b z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hz : 0 ≤ z) :
    (∫ t : ℝ in a..b, twoShiftReflectedDensity z t) ≤
      ∑ k ∈ Finset.range 6,
        (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k a := by
  let c := fun k : ℕ ↦ (Nat.choose 5 k : ℝ) * z ^ (5 - k)
  have hi (k : ℕ) :
    IntervalIntegrable (fun t ↦ c k * eulerMoment570 (13 / 25) k t) MeasureTheory.volume a b := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact
      (Analysis.log_power_tail_integrable (by norm_num only) ha k).mono_set Set.Ioc_subset_Ioi_self
  have hex (t : ℝ) :
    twoShiftReflectedDensity z t = ∑ k ∈ Finset.range 6, c k * eulerMoment570 (13 / 25) k t := by
    unfold twoShiftReflectedDensity eulerMoment570 c
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
    ring
  rw [intervalIntegral.integral_congr (fun t _ ↦ hex t),
    intervalIntegral.integral_finsetSum (fun k _ ↦ hi k)]
  apply Finset.sum_le_sum
  intro k _
  rw [intervalIntegral.integral_const_mul, eulerMoment570_interval (by norm_num only) ha hab]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))
  apply sub_le_self
  exact
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (ha.trans hab)) _)
      (Analysis.log_power_tail_poly_nonneg (by norm_num only) (Real.log_nonneg (ha.trans hab)) k)

/-- Under RH a bound on the slope integral alone controls the infinite reflected
Mangoldt tail, with its lower Chebyshev boundary and all main moments explicit. -/
theorem twoShiftReflected_tail_of_error (hRH : RiemannHypothesis) {a z D : ℝ} (ha : 101 ≤ a)
    (hz : 0 ≤ z) (hl : 5 ≤ Real.log a + z)
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b,
            Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t) ≤
          D) :
    let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      (∑ k ∈ Finset.range 6,
            (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k a) -
          (Chebyshev.psi a - a) * twoShiftReflectedDensity z a +
        D := by
  apply twoShiftReflected_tail_upper hRH ha hl _ hd
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact twoShiftReflected_main_upper (by linarith only [ha]) hb hz

/-- Coefficient of log(t)^k in the polynomial (38/25)(log(t)+z)^5-5(log(t)+z)^4.
The square logarithm in the RH envelope increases the moment degree by two. -/
noncomputable def twoShiftSlopeCoeff (z : ℝ) (k : ℕ) : ℝ :=
  ((38 / 25) * (Nat.choose 5 k : ℝ) * z ^ (5 - k) - 5 * (Nat.choose 4 k : ℝ) * z ^ (4 - k)) / 24

private theorem twoShiftSlopeCoeff_nonneg {z : ℝ} (hz : 4 ≤ z) {k : ℕ} (hk : k < 6) :
    0 ≤ twoShiftSlopeCoeff z k := by
  have hy := sub_nonneg.mpr hz
  generalize he : z - 4 = y at hy
  have hz' : z = y + 4 := by linarith only [he]
  rw [hz']
  unfold twoShiftSlopeCoeff
  interval_cases k <;>
    norm_num only [Nat.choose, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, Nat.reduceSub,
      Nat.reduceAdd] <;>
    ring_nf <;>
    positivity

/-- Under a shift of at least four the full RH slope error integral is bounded by
six nonnegative logarithmic moments of degrees two through seven at its lower endpoint. -/
theorem twoShiftReflected_error_moments {a b z : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hz : 4 ≤ z) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t) ≤
      ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) a := by
  have hi (k : ℕ) :
    IntervalIntegrable (fun t ↦ twoShiftSlopeCoeff z k * eulerMoment570 (51 / 50) (k + 2) t)
      MeasureTheory.volume a b := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
    exact
      (Analysis.log_power_tail_integrable (by norm_num only) ha (k + 2)).mono_set
        Set.Ioc_subset_Ioi_self
  have hex (t : ℝ) (ht : t ∈ Set.uIcc a b) :
    Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv (twoShiftReflectedDensity z) t =
      ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMoment570 (51 / 50) (k + 2) t := by
    have hp := zero_lt_one.trans_le (ha.trans ((Set.uIcc_of_le hab ▸ ht).1))
    have hpow : Real.sqrt t * t ^ (-(38 / 25 : ℝ) - 1) = t ^ (-(51 / 50 : ℝ) - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
      norm_num only
    rw [(twoShiftReflected_deriv z hp).deriv, neg_neg]
    unfold eulerMoment570 twoShiftSlopeCoeff
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero]
    norm_num only at hpow
    linear_combination
      (Real.log t ^ 2 / 24 * ((38 / 25) * (Real.log t + z) ^ 5 - 5 * (Real.log t + z) ^ 4)) * hpow
  rw [intervalIntegral.integral_congr hex, intervalIntegral.integral_finsetSum (fun k _ ↦ hi k)]
  apply Finset.sum_le_sum
  intro k hk
  rw [intervalIntegral.integral_const_mul, eulerMoment570_interval (by norm_num only) ha hab]
  apply
    mul_le_mul_of_nonneg_left (sub_le_self _ _)
      (twoShiftSlopeCoeff_nonneg hz (Finset.mem_range.mp hk))
  exact
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (ha.trans hab)) _)
      (Analysis.log_power_tail_poly_nonneg (by norm_num only) (Real.log_nonneg (ha.trans hab))
        (k + 2))

/-- Under RH the infinite shifted Mangoldt tail above a is bounded by the main
moments, the lower boundary envelope, and the six error moments in (96.22). -/
theorem twoShiftReflected_tail_closed (hRH : RiemannHypothesis) {a z : ℝ} (ha : 101 ≤ a)
    (hz : 4 ≤ z) (hl : 5 ≤ Real.log a + z) :
    let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      (∑ k ∈ Finset.range 6,
          (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k a) +
        Real.sqrt a * (Real.log a ^ 2 / 24) * twoShiftReflectedDensity z a +
        ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) a := by
  have he :=
    twoShiftReflected_tail_of_error hRH ha (by linarith only [hz]) hl (D :=
      ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) a)
      (by
        filter_upwards [Filter.eventually_ge_atTop a] with b hb using
          twoShiftReflected_error_moments (by linarith only [ha]) hb hz)
  have hf : 0 ≤ twoShiftReflectedDensity z a :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [ha]) _) (pow_nonneg (by linarith only [hl]) _)
  have h := mul_le_mul_of_nonneg_right (abs_le.mp (psi_log_sq_of_RH hRH ha)).1 hf
  linarith only [he, h]

/-- The closed RH bound applies to the reflected series indexed strictly beyond
the floor of the cutoff. The zero-index weight vanishes in the finite prefix. -/
theorem twoShiftReflected_tail_subtype (hRH : RiemannHypothesis) {a z : ℝ} (ha : 101 ≤ a)
    (hz : 4 ≤ z) (hl : 5 ≤ Real.log a + z) :
    (∑' n : { n : ℕ // ⌊a⌋₊ < n },
        ArithmeticFunction.vonMangoldt n.val * twoShiftReflectedDensity z n.val) ≤
      (∑ k ∈ Finset.range 6,
          (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k a) +
        Real.sqrt a * (Real.log a ^ 2 / 24) * twoShiftReflectedDensity z a +
        ∑ k ∈ Finset.range 6, twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) a := by
  let f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity z n
  have hp := (twoShiftReflected_summable z).sum_add_tsum_compl (s := Finset.Icc 0 ⌊a⌋₊)
  change
    (∑ n ∈ Finset.Icc 0 ⌊a⌋₊, f n) + (∑' n : { n : ℕ // n ∉ Finset.Icc 0 ⌊a⌋₊ }, f n.val) =
      ∑' n, f n at hp
  have he : (fun n : ℕ ↦ n ∉ Finset.Icc 0 ⌊a⌋₊) = (fun n : ℕ ↦ ⌊a⌋₊ < n) := by
    funext n
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le]
  rw [he, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)] at hp
  have hf : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_mul]
  rw [hf, add_zero] at hp
  change (∑' n : { n : ℕ // ⌊a⌋₊ < n }, f n.val) ≤ _
  calc
    _ = (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n := by linarith only [hp]
    _ ≤ _ := twoShiftReflected_tail_closed hRH ha hz hl

/-- The scaled fifth power in the reflected kernel decreases in the logarithmic
cutoff once it exceeds six, uniformly for every nonnegative log index. -/
theorem reflected_shift_antitone {v : ℝ} (hv : 0 ≤ v) :
    AntitoneOn (fun u : ℝ ↦ Real.exp (-(51 / 50) * u) * (v + (u - 1 / 5)) ^ 5) (Set.Ici 6) := by
  have hd (u : ℝ) :=
    (((hasDerivAt_id u).const_mul (-(51 / 50 : ℝ))).exp).mul
      ((((hasDerivAt_id u).sub_const (1 / 5)).const_add v).pow 5)
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun u _ ↦ (hd u).continuousAt.continuousWithinAt
  · exact fun u _ ↦ (hd u).differentiableAt.differentiableWithinAt
  · intro u hu
    have hu' : 6 ≤ u := interior_subset hu
    rw [(show HasDerivAt (fun x : ℝ ↦ Real.exp (-(51 / 50) * x) * (v + (x - 1 / 5)) ^ 5) _ u from
          hd u).deriv]
    dsimp only [id_eq, Pi.pow_apply]
    have h :=
      mul_nonneg
        (mul_nonneg (Real.exp_pos (-(51 / 50) * u)).le
          (pow_nonneg (show 0 ≤ v + (u - 1 / 5) by linarith only [hv, hu']) 4))
        (show 0 ≤ (51 / 50) * (v + (u - 1 / 5)) - 5 by linarith only [hv, hu'])
    linarith only [show
        0 ≤ Real.exp (-(51 / 50) * u) * (v + (u - 1 / 5)) ^ 4 * ((51 / 50) * (v + (u - 1 / 5)) - 5)
        from h]

/-- The reflected tail with the cutoff-dependent scaling of (96.22).
The remaining kernel multiplier is independent of the cutoff. -/
@[expose]
noncomputable def twoShiftReflectedTail (X : ℝ) : ℝ :=
  Real.exp (-(51 / 50) * Real.log X) *
    ∑' n : { n : ℕ // ⌊X⌋₊ < n },
      ArithmeticFunction.vonMangoldt n.val * twoShiftReflectedDensity (Real.log X - 1 / 5) n.val

/-- Enlarging a positive cutoff whose logarithm is at least six decreases the
scaled reflected tail: each retained term decreases and omitted terms are nonnegative. -/
theorem twoShiftReflectedTail_le {A X : ℝ} (hA : 0 < A) (hl : 6 ≤ Real.log A) (hX : A ≤ X) :
    twoShiftReflectedTail X ≤ twoShiftReflectedTail A := by
  let f := fun (x : ℝ) (n : ℕ) ↦
    Real.exp (-(51 / 50) * Real.log x) *
      (ArithmeticFunction.vonMangoldt n * twoShiftReflectedDensity (Real.log x - 1 / 5) n)
  have hs (x : ℝ) : Summable (fun n : { n : ℕ // ⌊x⌋₊ < n } ↦ f x n.val) :=
    ((twoShiftReflected_summable (Real.log x - 1 / 5)).mul_left _).subtype _
  let e := fun n : { n : ℕ // ⌊X⌋₊ < n } ↦
    (⟨n.val, lt_of_le_of_lt (Nat.floor_mono hX) n.property⟩ : { n : ℕ // ⌊A⌋₊ < n })
  have hlog := Real.log_le_log hA hX
  unfold twoShiftReflectedTail
  rw [← tsum_mul_left, ← tsum_mul_left]
  have hinj : Function.Injective e := fun _ _ he ↦
    Subtype.ext (congrArg (fun m : { n : ℕ // ⌊A⌋₊ < n } ↦ m.val) he)
  apply Summable.tsum_le_tsum_of_inj e hinj _ _ (hs X) (hs A)
  · intro n _
    apply mul_nonneg (Real.exp_pos _).le
    apply mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    exact
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (pow_nonneg (by linarith only [hl, Real.log_natCast_nonneg n.val]) _)
  · intro n
    have h := reflected_shift_antitone (Real.log_natCast_nonneg n.val) hl (hl.trans hlog) hlog
    have hw :=
      mul_le_mul_of_nonneg_left h
        (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n.val))
          (Real.rpow_nonneg (Nat.cast_nonneg n.val) (-(38 / 25 : ℝ))))
    dsimp only [f, e, twoShiftReflectedDensity]
    linarith only [hw]

/-- At every cutoff above 292 squared, evaluate the RH majorant at the fixed
entrance. The bound is independent of the moving cutoff and keeps the exact slope polynomial. -/
theorem twoShiftReflectedTail_upper (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X) :
    let A := (85264 : ℝ)
    let z := Real.log A - 1 / 5
    twoShiftReflectedTail X ≤
      A ^ (-(51 / 50 : ℝ)) *
        ((∑ k ∈ Finset.range 6,
            (Nat.choose 5 k : ℝ) * z ^ (5 - k) * eulerMomentValue570 (13 / 25) k A) +
          Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftReflectedDensity z A +
          ∑ k ∈ Finset.range 6,
            twoShiftSlopeCoeff z k * eulerMomentValue570 (51 / 50) (k + 2) A) := by
  intro A z
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 85264) (j := 16) (n := 16) (lo := 11) (hi := 12)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  change 11 ≤ Real.log A at hlo
  apply (twoShiftReflectedTail_le (by norm_num only [A]) (by linarith only [hlo]) hX).trans
  unfold twoShiftReflectedTail
  rw [Real.rpow_def_of_pos (by norm_num only [A] : 0 < A), mul_comm (Real.log A)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply twoShiftReflected_tail_subtype hRH (by norm_num only [A])
  · linarith only [hlo]
  · linarith only [hlo]

private theorem reflected_power_box (p d : ℕ) (u : ℚ)
    (h : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 85264 0 u p d = true) :
    (85264 : ℝ) ^ (-(p : ℝ) / d) ≤ (u : ℝ) := by
  exact (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound h).2

/-- With the sixth-pole normalization, the full reflected tail is below 0.005262
at every cutoff at least 292 squared under RH. Rational endpoints enclose each moment. -/
theorem twoShiftReflectedTail_numeric (hRH : RiemannHypothesis) {X : ℝ} (hX : 85264 ≤ X) :
    (51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X <
      5262 / 1000000 := by
  let L := Real.log 85264
  let z := L - 1 / 5
  let U := (113535077 / 10000000 : ℝ)
  let Z := U - 1 / 5
  let W := (113535076 / 10000000 : ℝ) - 1 / 5
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 85264) (j := 16) (n := 24) (lo :=
      113535076 / 10000000) (hi := 113535077 / 10000000) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  change _ ≤ L ∧ L ≤ U at hl
  have hL : 0 ≤ L := Real.log_nonneg (by norm_num only)
  have hz : 0 ≤ z := by
    dsimp only [z]; linarith only [hl.1]
  have hzU : z ≤ Z := sub_le_sub_right hl.2 _
  have hzW : W ≤ z := by
    dsimp only [W, z]; linarith only [hl.1]
  have hW : 0 ≤ W := by norm_num only [W]
  have hd := reflected_power_box 13 25 (27289894 / 10000000000) (by decide +kernel)
  have ha := reflected_power_box 51 50 (93458539 / 10000000000000) (by decide +kernel)
  have hs := reflected_power_box 38 25 (32006349 / 1000000000000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at hd ha hs
  let M := fun (d : ℝ) (k : ℕ) ↦ Analysis.logPowerTailPoly d k U
  have hm {d P : ℝ} (hp : 0 < d) (hP : (85264 : ℝ) ^ (-d) ≤ P) (k : ℕ) :
    eulerMomentValue570 d k 85264 ≤ P * M d k := by
    apply
      mul_le_mul hP (Analysis.log_power_tail_poly_mono hp hL hl.2 k)
        (Analysis.log_power_tail_poly_nonneg hp hL k)
    exact (Real.rpow_nonneg (by norm_num only) _).trans hP
  let C := fun k : ℕ ↦
    ((38 / 25) * (Nat.choose 5 k : ℝ) * Z ^ (5 - k) - 5 * (Nat.choose 4 k : ℝ) * W ^ (4 - k)) / 24
  have hc (k : ℕ) : twoShiftSlopeCoeff z k ≤ C k := by
    apply div_le_div_of_nonneg_right _ (by norm_num only)
    exact
      sub_le_sub (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzU _) (by positivity))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hW hzW _) (by positivity))
  have hmain :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun k _ ↦
        mul_le_mul
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hzU (5 - k))
            (Nat.cast_nonneg (Nat.choose 5 k)))
          (hm (by norm_num only) hd k)
          (show 0 ≤ eulerMomentValue570 (13 / 25) k 85264 from
            mul_nonneg (Real.rpow_nonneg (by norm_num only) _)
              (Analysis.log_power_tail_poly_nonneg (by norm_num only) hL k))
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hz.trans hzU) _)))
  have herr :=
    Finset.sum_le_sum (s := Finset.range 6)
      (fun k hk ↦
        mul_le_mul (hc k) (hm (by norm_num only) ha (k + 2))
          (show 0 ≤ eulerMomentValue570 (51 / 50) (k + 2) 85264 from
            mul_nonneg (Real.rpow_nonneg (by norm_num only) _)
              (Analysis.log_power_tail_poly_nonneg (by norm_num only) hL _))
          ((twoShiftSlopeCoeff_nonneg
                (show 4 ≤ z by
                  dsimp only [z]; linarith only [hl.1])
                (Finset.mem_range.mp hk)).trans
            (hc k)))
  have hden :=
    mul_le_mul hs (pow_le_pow_left₀ (add_nonneg hL hz) (add_le_add hl.2 hzU) 5)
      (pow_nonneg (add_nonneg hL hz) _) (by norm_num only)
  have hb :=
    mul_le_mul
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ hL hl.2 2) (by norm_num only : (0 : ℝ) ≤ 24))
      hden (mul_nonneg (Real.rpow_nonneg (by norm_num only) _) (pow_nonneg (add_nonneg hL hz) _))
      (by positivity)
  have ht := twoShiftReflectedTail_upper hRH hX
  have hroot : Real.sqrt 85264 = 292 := by norm_num only [Real.sqrt_eq_iff_mul_self_eq_of_pos]
  dsimp only at ht
  rw [hroot] at ht
  have hsum :=
    add_le_add (add_le_add hmain (mul_le_mul_of_nonneg_left hb (by norm_num only : (0 : ℝ) ≤ 292)))
      herr
  have hsum' : _ ≤ (499014 / 10 : ℝ) :=
    le_trans hsum
      (by
        norm_num only [C, M, W, U, Z, Analysis.logPowerTailPoly, Finset.sum_range_succ,
          Finset.sum_range_zero, Nat.choose, Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have hu : twoShiftReflectedTail X ≤ (93458539 / 10000000000000 : ℝ) * (499014 / 10) := by
    apply ht.trans
    apply
      le_trans (mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by norm_num only) _))
        (mul_le_mul_of_nonneg_right ha (by norm_num only))
    dsimp only [twoShiftReflectedDensity, z, L] at hsum'
    unfold twoShiftReflectedDensity
    linarith only [hsum']
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 5)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero] at he
  have h := mul_le_mul_of_nonneg_left hu (Real.exp_pos ((51 / 50) * (1 / 5))).le
  nlinarith only [h, he]

/-- Under RH the explicit normalized reflected tail meets the required budget for
the three Jacobi characters when the logarithmic input is at least 950. -/
theorem pair_twoShift_reflected_remainder (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L X : ℝ} (hL : 950 ≤ L) (hX : L ^ 2 / 4 ≤ X)
    (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-1 / 8 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
          twoShiftConductor (2 * Real.log (L / 2)) +
          twoShiftReciprocalCoeff / (L / 2) -
        2 *
          ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X) := by
  apply pair_twoShift_large_remainder p q r hp hq hr hL hX hRH
  have hcut : 85264 ≤ X := by nlinarith only [hL, hX, sq_nonneg (L - 950)]
  linarith only [twoShiftReflectedTail_numeric hRH hcut]

/-- For a cutoff X beyond A, the unsigned Euler tail is bounded by the closed
RH envelope evaluated at A. Every summand removed between the two floors is nonnegative. -/
theorem twoShiftEuler_tail_endpoint (hRH : RiemannHypothesis) {A X : ℝ} (ha : 101 ≤ A)
    (hx : A ≤ X) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤
      twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A := by
  intro f
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 101) (j := 7) (n := 16) (lo := 4) (hi := 5)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog
  have hp : ∑ n ∈ Finset.Ioc 0 ⌊A⌋₊, f n ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl (Nat.floor_mono hx))
    intro n hn hout
    have hgt : ⌊A⌋₊ < n :=
      lt_of_not_ge (fun h ↦ hout (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, h⟩))
    have hl : (101 : ℝ) ≤ n := Nat.cast_le.mpr ((Nat.le_floor ha).trans hgt.le)
    exact
      mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (twoShiftEulerPoly_pos (hlog.trans (Real.log_le_log (by norm_num only) hl))).le
  exact (sub_le_sub_left hp _).trans (twoShiftEuler_tail_closed hRH ha)

/-- Uniform lower bound on a whole radius interval in (96.25). Evaluate the unsigned
Euler cap and the conductor at the left endpoint, and the reciprocal correction at the right. -/
theorem pair_twoShift_interval_remainder (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {u v R X : ℝ} (hu : 292 ≤ u) (huR : u ≤ R) (hRv : R ≤ v)
    (hX : R ^ 2 ≤ X) (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    let A := u ^ 2
    1334316 / 1000000 -
            4 *
              (twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
                twoShiftEulerError A) +
          twoShiftConductor (2 * Real.log u) +
          (88098 / 10000) / v -
        2 * (5262 / 1000000) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
          twoShiftConductor (2 * Real.log R) +
          twoShiftReciprocalCoeff / R -
        2 *
          ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X) := by
  intro a b c f D A
  have hu0 : 0 < u := by linarith only [hu]
  have hA : 85264 ≤ A := by
    dsimp only [A]; nlinarith only [hu, sq_nonneg (u - 292)]
  have hAX := (pow_le_pow_left₀ hu0.le huR 2).trans hX
  have h101 : 101 ≤ A := by linarith only [hA]
  have he := twoShiftEuler_tail_endpoint hRH h101 hAX
  have ht :=
    three_trace_tail_residual a b c (h101.trans hAX)
      (by
        intro n
        simpa only [Int.cast_natCast] using
          pair_character_sum_ge_neg_one (n : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr))
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 227 / 40) (hi :=
        6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hbase : 227 / 20 ≤ 2 * Real.log u := by
    linarith only [hlog, Real.log_le_log (by norm_num only) hu]
  have hstep := mul_le_mul_of_nonneg_left (Real.log_le_log hu0 huR) zero_le_two
  have hc := twoShiftConductor_monotone hbase (hbase.trans hstep) hstep
  have hR := hu0.trans_le huR
  have hrec :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 88098 / 10000) hR hRv).trans_lt
      (div_lt_div_of_pos_right twoShiftReciprocalCoeff_lower hR)
  have href := twoShiftReflectedTail_numeric hRH (hA.trans hAX)
  dsimp only at he ht
  dsimp only [D, f]
  linarith only [twoShiftPoleConstant_lower, he, ht, hc, hrec, href]

/-- The signed remainder exceeds −0.13 throughout the first interval from 292 to 292.25
under RH, using the sharpened Euler cap at the entrance. -/
theorem pair_twoShift_first_interval (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {R X : ℝ} (huR : 292 ≤ R) (hRv : R ≤ 1169 / 4) (hX : R ^ 2 ≤ X)
    (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-13 / 100 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
          twoShiftConductor (2 * Real.log R) +
          twoShiftReciprocalCoeff / R -
        2 *
          ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp ((51 / 50) * (1 / 5)) * twoShiftReflectedTail X) := by
  intro a b c f D
  have h := pair_twoShift_interval_remainder p q r hp hq hr le_rfl huR hRv hX hRH
  dsimp only at h
  have hc := twoShiftConductor_lower (r := 292) le_rfl
  have he := twoShiftEuler_cap_292
  dsimp only at he
  dsimp only [a, b, c, f, D]
  linarith only [h, hc, he]

end PseudoPrime.PrimeTestBounds.MillerRabin
