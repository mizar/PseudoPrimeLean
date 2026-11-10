/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogSquarePowerIntegral

/-! # Higher logarithmic power tail integrals -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The polynomial appearing in the tail integral of `log(t)^k * t^(-r-1)`.
The recurrence adds the leading monomial and the integrated lower degree. -/
noncomputable def logPowerTailPoly (r : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1 / r
  | k + 1, z => z ^ (k + 1) / r + ((k + 1 : ℕ) : ℝ) / r * logPowerTailPoly r k z

/-- Every tail polynomial is nonnegative at a nonnegative logarithmic
argument when the decay rate is positive. -/
theorem log_power_tail_poly_nonneg {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (k : ℕ) :
    0 ≤ logPowerTailPoly r k z := by
  induction k with
  | zero =>
    dsimp only [logPowerTailPoly]
    exact div_nonneg zero_le_one hr.le
  | succ k ih =>
    dsimp only [logPowerTailPoly]
    exact
      add_nonneg (div_nonneg (pow_nonneg hz _) hr.le)
        (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hr.le) ih)

/-- For a positive decay rate, every tail polynomial is nondecreasing
on the nonnegative half-line. This transfers rational logarithm endpoints. -/
theorem log_power_tail_poly_mono {r z Z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (hZ : z ≤ Z) (k : ℕ) :
    logPowerTailPoly r k z ≤ logPowerTailPoly r k Z := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    dsimp only [logPowerTailPoly]
    exact
      add_le_add (div_le_div_of_nonneg_right (pow_le_pow_left₀ hz hZ _) hr.le)
        (mul_le_mul_of_nonneg_left ih (div_nonneg (Nat.cast_nonneg _) hr.le))

/-- The derivative of the tail polynomial equals `r` times the polynomial
minus its leading monomial. This is the identity behind its antiderivative. -/
theorem log_power_tail_poly_deriv {r : ℝ} (hr : 0 < r) (k : ℕ) (z : ℝ) :
    HasDerivAt (logPowerTailPoly r k) (r * logPowerTailPoly r k z - z ^ k) z := by
  induction k with
  | zero =>
    have h := hasDerivAt_const z (1 / r)
    convert h using 1
    · rfl
    · dsimp only [logPowerTailPoly]
      field_simp [hr.ne']
      norm_num only
  | succ k
    ih =>
    have h :=
      (((hasDerivAt_id z).pow (k + 1)).div_const r).add (ih.const_mul (((k + 1 : ℕ) : ℝ) / r))
    apply h.congr_deriv
    dsimp only [logPowerTailPoly]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, id_eq]
    field_simp [hr.ne']
    ring

/-- The negative power times the tail polynomial is an antiderivative of
the corresponding logarithmic moment on the positive half-line. -/
theorem log_power_tail_primitive_deriv {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (k : ℕ) :
    HasDerivAt (fun x : ℝ ↦ -x ^ (-r) * logPowerTailPoly r k (Real.log x))
      (Real.log t ^ k * t ^ (-r - 1)) t := by
  have hp := (Real.hasDerivAt_rpow_const (p := -r) (Or.inl ht.ne')).neg
  have hl := (log_power_tail_poly_deriv hr k (Real.log t)).comp t (Real.hasDerivAt_log ht.ne')
  have h := hp.mul hl
  apply h.congr_deriv
  dsimp only [Pi.neg_apply, Function.comp_apply]
  rw [Real.rpow_sub_one ht.ne' (-r)]
  ring

/-- Every logarithmic power multiplied by a negative real power tends to zero
at infinity. The logarithmic little-o estimate supplies this uniformly in degree. -/
theorem log_pow_mul_neg_rpow_tendsto {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Filter.Tendsto (fun t : ℝ ↦ t ^ (-r) * Real.log t ^ k) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun t : ℝ ↦ Real.log t ^ k / t ^ r) Filter.atTop (nhds 0) := by
    simpa only [Real.rpow_natCast] using
      (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht]
  ring

/-- The polynomial antiderivative tends to zero at infinity for every
nonnegative logarithmic degree and positive power exponent. -/
theorem log_power_tail_primitive_tendsto {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Filter.Tendsto (fun t : ℝ ↦ -t ^ (-r) * logPowerTailPoly r k (Real.log t)) Filter.atTop
      (nhds 0) := by
  have hp :
    Filter.Tendsto (fun t : ℝ ↦ t ^ (-r) * logPowerTailPoly r k (Real.log t)) Filter.atTop
      (nhds 0) := by
    induction k with
    | zero =>
      simpa only [logPowerTailPoly, zero_mul] using (tendsto_rpow_neg_atTop hr).mul_const (1 / r)
    | succ k ih =>
      have h1 := (log_pow_mul_neg_rpow_tendsto hr (k + 1)).div_const r
      have h2 := ih.const_mul (((k + 1 : ℕ) : ℝ) / r)
      have h := h1.add h2
      simp only [zero_div, mul_zero, zero_add] at h
      apply h.congr
      intro t
      dsimp only [logPowerTailPoly]
      ring
  have hn := hp.neg
  simpa only [neg_zero, neg_mul] using hn

/-- For positive decay and cutoff at least one, every nonnegative logarithmic
power moment is integrable on the tail. The explicit primitive tends to zero. -/
theorem log_power_tail_integrable {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) (k : ℕ) :
    MeasureTheory.IntegrableOn (fun t : ℝ ↦ Real.log t ^ k * t ^ (-r - 1)) (Set.Ioi a) := by
  exact
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg'
      (fun x hx ↦ log_power_tail_primitive_deriv hr (zero_lt_one.trans_le (ha.trans hx)) k)
      (fun x hx ↦
        mul_nonneg (pow_nonneg (Real.log_nonneg (ha.trans hx.le)) k)
          (Real.rpow_nonneg (zero_le_one.trans (ha.trans hx.le)) _))
      (log_power_tail_primitive_tendsto hr k)

/-- Evaluate every logarithmic power moment above a cutoff at least one.
The result is the negative-power endpoint times its explicit tail polynomial. -/
theorem log_power_tail_integral {r a : ℝ} (hr : 0 < r) (ha : 1 ≤ a) (k : ℕ) :
    (∫ t in Set.Ioi a, Real.log t ^ k * t ^ (-r - 1)) =
      a ^ (-r) * logPowerTailPoly r k (Real.log a) := by
  have h :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx ↦ log_power_tail_primitive_deriv hr (zero_lt_one.trans_le (ha.trans hx)) k)
      (log_power_tail_integrable hr ha k) (log_power_tail_primitive_tendsto hr k)
  simp only [zero_sub, neg_mul, neg_neg] at h
  exact h

end PseudoPrime.Analysis
