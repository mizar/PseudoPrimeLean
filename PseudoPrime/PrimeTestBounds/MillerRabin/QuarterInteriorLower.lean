/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointLower

/-! # Interior joint Abel lower bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, a nonnegative joint Abel weight preserves the explicit
Chebyshev lower bound on the interval from 16 to the support scale. The
weight parameter may exceed half the logarithmic scale. -/
theorem quarter_interior_integrand_lower (hRH : RiemannHypothesis) {a X t : ℝ} (hX : 1 ≤ X)
    (hbound : Real.log X ≤ 2 * a) (ht : 16 ≤ t) (htX : t ≤ X) :
    (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
        (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000) ≤
      (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t := by
  have hp : 0 < t := by linarith only [ht]
  have hl := Real.log_le_log hp htX
  have ha : 0 ≤ a := by
    have hlog := Real.log_nonneg hX
    linarith only [hlog, hbound]
  have hd : 0 ≤ t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2) :=
    mul_nonneg (Real.rpow_nonneg hp.le _) (by linarith only [hl, hbound, ha])
  exact mul_le_mul_of_nonneg_left (LLS.PaperStatements.scaleOne_psi_lower hRH ht) hd

/-- Under RH, the joint Abel integral is at least the explicit Chebyshev
lower-bound integral from 16 to the support endpoint. The omitted interval
from one to 16 contributes nonnegatively. -/
theorem quarter_interior_integral_lower (hRH : RiemannHypothesis) {a X : ℝ} (hX : 16 ≤ X)
    (hbound : Real.log X ≤ 2 * a) :
    (∫ t in (16 : ℝ)..X,
        (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
          (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)) ≤
      ∫ t in (1 : ℝ)..X, (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)
  let p := fun t : ℝ ↦
    d t * (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)
  have hX1 : (1 : ℝ) ≤ X := by linarith only [hX]
  have ha : 0 ≤ a := by
    have h := Real.log_nonneg hX1
    linarith only [h, hbound]
  have hdcont {u v : ℝ} (hu : 1 ≤ u) : ContinuousOn d (Set.Icc u v) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le (hu.trans ht.1)
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have hint {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume u v := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (by linarith only [hu])
        (hdcont (u := u) (v := v) hu).integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hpcont : ContinuousOn p (Set.Icc 16 X) := by
    intro t ht
    have hp : 0 < t := by linarith only [ht.1]
    have hr (r : ℝ) := Real.continuousAt_rpow_const t r (Or.inl hp.ne')
    have hdt := (hdcont (u := 16) (v := X) (by norm_num only) t ht)
    have hc :
      ContinuousAt
        (fun z : ℝ ↦
          z - (19 / 30 : ℝ) * z ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * z ^ (1 / 4 : ℝ) - 1839 / 1000)
        t :=
      ((continuousAt_id.sub ((hr (3 / 4)).const_mul (19 / 30))).sub
            ((hr (1 / 4)).const_mul (63 / 10))).sub_const
        (1839 / 1000)
    exact hdt.mul hc.continuousWithinAt
  have hpint : IntervalIntegrable p MeasureTheory.volume 16 X := hpcont.intervalIntegrable_of_Icc hX
  have hlo : 0 ≤ ∫ t in (1 : ℝ)..16, d t * Chebyshev.psi t := by
    have hm :=
      intervalIntegral.integral_mono_on (by norm_num only : (1 : ℝ) ≤ 16) intervalIntegrable_const
        (hint (by norm_num only) (by norm_num only))
        (fun t ht ↦ by
          have htX : t ≤ X := ht.2.trans hX
          have hp : 0 < t := zero_lt_one.trans_le ht.1
          have hl := Real.log_le_log hp htX
          have hd0 : 0 ≤ d t :=
            mul_nonneg (Real.rpow_nonneg hp.le _) (by linarith only [hl, hbound, ha])
          exact mul_nonneg hd0 (Chebyshev.psi_nonneg t))
    simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_zero] using hm
  have hhi : (∫ t in (16 : ℝ)..X, p t) ≤ ∫ t in (16 : ℝ)..X, d t * Chebyshev.psi t := by
    apply intervalIntegral.integral_mono_on hX hpint (hint (by norm_num only) hX)
    intro t ht
    exact quarter_interior_integrand_lower hRH hX1 hbound ht.1 ht.2
  have hsum :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 16)) (hint (by norm_num only) hX)
  change (∫ t in (16 : ℝ)..X, p t) ≤ ∫ t in (1 : ℝ)..X, d t * Chebyshev.psi t
  linarith only [hlo, hhi, hsum]

end PseudoPrime.PrimeTestBounds.MillerRabin
