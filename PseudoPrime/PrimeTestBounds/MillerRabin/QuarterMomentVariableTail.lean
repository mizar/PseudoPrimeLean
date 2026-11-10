/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentInfiniteTail

/-! Infinite Euler moment tails at variable cutoffs. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The Euler moment tail integrand is integrable above any cutoff at least one. This permits
passing the finite Chebyshev-envelope estimate to an arbitrary real cutoff. -/
theorem quarter_moment_integrable_from (k : ℕ) {a : ℝ} (ha : 1 ≤ a) :
    MeasureTheory.IntegrableOn (quarterMomentTailIntegrand k) (Set.Ioi a) := by
  have hbase :=
    ((target028_log_moment_integrable k).mono_set (Set.Ioi_subset_Ioi ha)).const_mul (7 / 4 : ℝ)
  apply hbase.mono' ?_ ?_
  · have hm : Measurable (quarterMomentTailIntegrand k) := by
      unfold quarterMomentTailIntegrand AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
      exact
        (measurable_const.add (measurable_const.mul (measurable_id.pow_const _))).mul
          ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const k))
    exact hm.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := ha.trans ht.le
    have hw : 0 ≤ target028LogMoment k t :=
      mul_nonneg (pow_nonneg (Real.log_nonneg ht1) k) (Real.rpow_nonneg (by linarith only [ht1]) _)
    have hp := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num only : -(1 / 4 : ℝ) ≤ 0)
    have hf : 1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)) ≤ 7 / 4 := by linarith only [hp]
    have h := mul_le_mul_of_nonneg_right hf hw
    rw [Real.norm_of_nonneg (quarter_moment_tail_integrand_nonneg k ht1)]
    simpa only [quarterMomentTailIntegrand, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight,
      target028LogMoment, mul_comm] using h

/-- A finite Mangoldt moment tail beginning after any natural cutoff tends to its infinite tail.
Summability and finite interval decomposition justify the limit. -/
theorem quarter_moment_tendsto_from (k m : ℕ) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc m N, quarterMangoldtMoment k n) Filter.atTop
      (nhds
        ((∑' n : ℕ, quarterMangoldtMoment k n) -
          ∑ n ∈ Finset.Ioc 0 m, quarterMangoldtMoment k n)) := by
  have hs :=
    (quarter_mangoldt_moment_summable k).hasSum.tendsto_sum_nat.comp
      (Filter.tendsto_add_atTop_nat 1)
  have hp :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc 0 N, quarterMangoldtMoment k n) Filter.atTop
      (nhds (∑' n : ℕ, quarterMangoldtMoment k n)) := by
    apply Filter.Tendsto.congr (fun N ↦ ?_) hs
    dsimp only [Function.comp_apply]
    rw [Nat.range_eq_Icc_zero_sub_one (N + 1) (Nat.add_one_ne_zero N), Nat.add_sub_cancel, ←
      Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le N)]
    simp only [quarterMangoldtMoment, ArithmeticFunction.map_zero, zero_mul, add_zero]
  have ht := hp.sub_const (∑ n ∈ Finset.Ioc 0 m, quarterMangoldtMoment k n)
  apply Filter.Tendsto.congr' ?_ ht
  apply (Filter.eventually_ge_atTop m).mono
  intro N hN
  have hd : Disjoint (Finset.Ioc 0 m) (Finset.Ioc m N) :=
    Finset.disjoint_left.mpr
      (fun n hn hm ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hn).2) (Finset.mem_Ioc.mp hm).1)
  have he := Finset.sum_union (f := quarterMangoldtMoment k) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hN] at he
  dsimp only
  linarith only [he]

/-- Under RH, a decreasing Euler moment has an infinite-tail upper bound at any real cutoff
at least 625. The exact cutoff correction is retained for a sharp numerical estimate. -/
theorem quarter_moment_infinite_from (hRH : RiemannHypothesis) (k : ℕ) {a : ℝ} (ha : 625 ≤ a)
    (hk : ∀ t : ℝ, a ≤ t → (k : ℝ) ≤ (79 / 50 : ℝ) * Real.log t) :
    (∑' n : ℕ, quarterMangoldtMoment k n) - (∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, quarterMangoldtMoment k n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a *
          (a + a ^ (3 / 4 : ℝ) - Chebyshev.psi a) +
        ∫ t in Set.Ioi a, quarterMomentTailIntegrand k t := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hn : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi a)] quarterMomentTailIntegrand k := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact quarter_moment_tail_integrand_nonneg k (ha1.trans ht.le)
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hevent := hcast.eventually (Filter.eventually_ge_atTop a)
  apply le_of_tendsto (quarter_moment_tendsto_from k ⌊a⌋₊)
  filter_upwards [hevent] with N hN
  have hf :=
    quarter_moment_tail_envelope hRH (79 / 50) k ha hN (by norm_num only) (fun t ht ↦ hk t ht.1)
  simp only [Nat.floor_natCast] at hf
  have he :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ N,
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k n *
          ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ N, quarterMangoldtMoment k n := by
    apply Finset.sum_congr rfl
    intro n hn'
    dsimp only [quarterMangoldtMoment, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight]
    ring
  rw [he] at hf
  have hi :=
    MeasureTheory.setIntegral_mono_set (quarter_moment_integrable_from k ha1) hn
      (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioc a (N : ℝ)) ↦ ht.1))
  change
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ N, quarterMangoldtMoment k n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k a *
          (a + a ^ (3 / 4 : ℝ) - Chebyshev.psi a) +
        ∫ t in Set.Ioc a (N : ℝ), quarterMomentTailIntegrand k t at hf
  linarith only [hf, hi]

end PseudoPrime.PrimeTestBounds.MillerRabin
