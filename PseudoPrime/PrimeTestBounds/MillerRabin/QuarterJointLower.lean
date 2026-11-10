/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterHighComparison
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneSharp

/-! # Lower bounds for the combined quarter-scale principal sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, the positive joint Abel weight preserves the explicit
Chebyshev lower bound at every point from 16 to the support endpoint. This
is the pointwise input for the joint principal lower estimate. -/
theorem quarter_joint_integrand_lower (hRH : RiemannHypothesis) {a X t : ℝ} (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) (ht : 16 ≤ t) (htX : t ≤ X) :
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
theorem quarter_joint_integral_lower (hRH : RiemannHypothesis) {a X : ℝ} (hX : 16 ≤ X)
    (hbound : Real.log X = 2 * a) :
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
    exact quarter_joint_integrand_lower hRH hX1 hbound ht.1 ht.2
  have hsum :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 16)) (hint (by norm_num only) hX)
  change (∫ t in (16 : ℝ)..X, p t) ≤ ∫ t in (1 : ℝ)..X, d t * Chebyshev.psi t
  linarith only [hlo, hhi, hsum]

/-- If no prime through `r²` rejects the input and the Fermat index exceeds
that cutoff, the explicit RH lower-bound integral and boundary term satisfy
the high-index upper comparison. This is the scalar inequality to contradict. -/
theorem quarter_high_explicit_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a r T : ℝ}
    (ha : 0 < a) (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) (hT : 0 ≤ T)
    (hscale : Real.log n ≤ T) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    (2 * a * (r ^ 2) ^ (-1 / 2 : ℝ)) * Chebyshev.psi (r ^ 2) +
        (∫ t in (16 : ℝ)..(r ^ 2),
          (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
            (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)) <
      2 * a * T + 31 := by
  have hr2 : (16 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 100), hr]
  have hlower := quarter_joint_integral_lower hGRH.riemann hr2 hbound
  rw [intervalIntegral.integral_of_le (by linarith only [hr2] : (1 : ℝ) ≤ r ^ 2)] at hlower
  have hupper := quarter_high_abel_cost hn ho ha hr hbound hT hscale hGRH hindex hnone
  linarith only [hlower, hupper]

/-- Under the high-index no-witness hypotheses, replace the remaining
Chebyshev boundary value by the same explicit RH lower estimate. Both terms
are now elementary expressions or integrals of elementary functions. -/
theorem quarter_high_elementary_cost {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n) {a r T : ℝ}
    (ha : 0 < a) (hr : 100 ≤ r) (hbound : Real.log (r ^ 2) = 2 * a) (hT : 0 ≤ T)
    (hscale : Real.log n ≤ T) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hindex : ⌊r ^ 2⌋₊ < (PrimeTest.fermatSubgroup n).index)
    (hnone :
      ¬∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ r ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) :
    (2 * a * (r ^ 2) ^ (-1 / 2 : ℝ)) *
          (r ^ 2 - (19 / 30 : ℝ) * (r ^ 2) ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * (r ^ 2) ^ (1 / 4 : ℝ) -
            1839 / 1000) +
        (∫ t in (16 : ℝ)..(r ^ 2),
          (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) *
            (t - (19 / 30 : ℝ) * t ^ (3 / 4 : ℝ) - (63 / 10 : ℝ) * t ^ (1 / 4 : ℝ) - 1839 / 1000)) <
      2 * a * T + 31 := by
  have hr2 : (16 : ℝ) ≤ r ^ 2 := by nlinarith only [sq_nonneg (r - 100), hr]
  have hψ := LLS.PaperStatements.scaleOne_psi_lower hGRH.riemann hr2
  have hcoef : 0 ≤ 2 * a * (r ^ 2) ^ (-1 / 2 : ℝ) :=
    mul_nonneg (by linarith only [ha]) (Real.rpow_nonneg (sq_nonneg r) _)
  have hboundary := mul_le_mul_of_nonneg_left hψ hcoef
  have hcost := quarter_high_explicit_cost hn ho ha hr hbound hT hscale hGRH hindex hnone
  linarith only [hboundary, hcost]

end PseudoPrime.PrimeTestBounds.MillerRabin
