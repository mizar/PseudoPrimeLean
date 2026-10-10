/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteMeasureIntervals
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ScaledMangoldtMeasure
public import PseudoPrime.LLS.RiemannChebyshevBounds
public import Mathlib.Topology.Order.ProjIcc

/-!
# Continuous weighted Mangoldt limits under RH

Scaled finite Mangoldt measures converge weakly to interval volume, using the endpoint
asymptotics for Chebyshev's psi. Extending a continuous interval weight by projection then
gives its weighted-sum limit. This supplies the truncated kernel comparison in Proposition 6.1.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH and a positive lower cutoff, the real mass assigned to any half-open interval
by a scaled cutoff Mangoldt measure tends to the positive part of the intersection length.
Use the endpoint psi limit when the intersection is nonempty and an empty finite sum otherwise.
This supplies all interval masses required for weak convergence. -/
theorem tendsto_scaledMangoldtMeasure_Ioc (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 < a)
    (c d : ℝ) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.scaledMangoldtMeasure (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊) x
            (Set.Ioc c d) :
          ℝ))
      Filter.atTop (nhds (max (min b d - max a c) 0)) := by
  have he : ∀ᶠ x : ℝ in Filter.atTop, 0 < x := Filter.eventually_gt_atTop 0
  by_cases hcd : max a c ≤ min b d
  · have h := tendsto_mangoldt_scaled_interval_sum hRH (ha.trans_le (le_max_left a c)) hcd
    rw [max_eq_left (sub_nonneg.mpr hcd)]
    apply h.congr'
    filter_upwards [he] with x hx
    exact (AnalyticNumberTheory.Arithmetic.scaledMangoldtMeasure_Ioc_real hx a b c d).symm
  · have hdc := le_of_lt (lt_of_not_ge hcd)
    rw [max_eq_right (sub_nonpos.mpr hdc)]
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with x hx
    rw [AnalyticNumberTheory.Arithmetic.scaledMangoldtMeasure_Ioc_real hx,
      Finset.Ioc_eq_empty_of_le (Nat.floor_mono (mul_le_mul_of_nonneg_right hdc hx.le)),
      Finset.sum_empty, zero_div]

/-- Under RH, normalized Mangoldt point masses on a fixed positive scaled interval converge
weakly to Lebesgue measure restricted to that interval. The endpoint asymptotics provide
total-mass and interval-mass convergence. This permits arbitrary bounded continuous weights. -/
theorem tendsto_scaledMangoldtMeasure (hRH : RiemannHypothesis) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    Filter.Tendsto
      (fun x : ℝ ↦
        AnalyticNumberTheory.Arithmetic.scaledMangoldtMeasure (Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊) x)
      Filter.atTop (nhds (Analysis.intervalVolume a b)) := by
  apply Analysis.tendsto_finiteMeasure_of_mass_and_Ioc
  · apply NNReal.tendsto_coe.mp
    rw [Analysis.intervalVolume_mass_real hab]
    apply (tendsto_mangoldt_scaled_interval_sum hRH ha hab).congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    exact (AnalyticNumberTheory.Arithmetic.scaledMangoldtMeasure_mass_real _ hx).symm
  · intro c d hcd
    apply NNReal.tendsto_coe.mp
    rw [Analysis.intervalVolume_Ioc_real]
    exact tendsto_scaledMangoldtMeasure_Ioc hRH ha c d

/-- Under RH, positive ordered interval endpoints and a continuous real weight on the closed
interval give convergence of the normalized weighted Mangoldt sum to its interval integral.
Extend the weight by projection onto the compact interval, apply weak convergence, and evaluate
the finite atomic integrals. This handles kernel weights without differentiability assumptions. -/
theorem tendsto_weighted_mangoldt_scaled_interval_sum (hRH : RiemannHypothesis) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto
      (fun x : ℝ ↦
        (∑ n ∈ Finset.Ioc ⌊a * x⌋₊ ⌊b * x⌋₊, ArithmeticFunction.vonMangoldt n * f ((n : ℝ) / x)) /
          x)
      Filter.atTop (nhds (∫ u in a..b, f u)) := by
  let fc : ContinuousMap (Set.Icc a b) ℝ := ⟨_, hf.domRestrict⟩
  let fb :=
    (BoundedContinuousFunction.mkOfCompact fc).compContinuous
      (⟨Set.projIcc a b hab, continuous_projIcc⟩ : ContinuousMap ℝ (Set.Icc a b))
  have hfb : ∀ u ∈ Set.Icc a b, fb u = f u := by
    intro u hu
    change f (Set.projIcc a b hab u) = f u
    rw [Set.projIcc_of_mem hab hu]
  have ht :=
    MeasureTheory.FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_scaledMangoldtMeasure hRH ha hab) fb
  have hi :
    (∫ u, fb u ∂(Analysis.intervalVolume a b : MeasureTheory.Measure ℝ)) = ∫ u in a..b, f u := by
    change (∫ u in Set.Ioc a b, fb u) = _
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_congr_Ioo_of_le hab (fun u hu ↦ hfb u ⟨hu.1.le, hu.2.le⟩)
  rw [hi] at ht
  apply ht.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  rw [AnalyticNumberTheory.Arithmetic.integral_scaledMangoldtMeasure _ hx]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Ioc.mp hn
  have hnne := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hn'.1)
  rw [hfb _
      (Set.Ioc_subset_Icc_self
        ((AnalyticNumberTheory.Arithmetic.mem_scaled_Ioc hx hnne a b).mp hn))]

end PseudoPrime.LLS
