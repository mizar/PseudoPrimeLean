/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTail

/-! # Infinite reflected moment tails -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive integrand left after cancellation of the upper Chebyshev
boundary. Its two terms have the power-logarithm form of the paper's tail. -/
noncomputable def quarterMomentTailIntegrand (k : ℕ) (t : ℝ) : ℝ :=
  (1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ))) *
    AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k t

/-- The tail integrand is nonnegative above one. -/
theorem quarter_moment_tail_integrand_nonneg (k : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    0 ≤ quarterMomentTailIntegrand k t := by
  unfold quarterMomentTailIntegrand AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hl := Real.log_nonneg ht
  positivity

/-- The tail integrand is integrable above 2701. Bound its extra inverse
quarter-power factor by one and use the established logarithmic moment. -/
theorem quarter_moment_tail_integrable (k : ℕ) :
    MeasureTheory.IntegrableOn (quarterMomentTailIntegrand k) (Set.Ioi 2701) := by
  have hbase :=
    ((target028_log_moment_integrable k).mono_set
          (Set.Ioi_subset_Ioi (by norm_num only : (1 : ℝ) ≤ 2701))).const_mul
      (7 / 4 : ℝ)
  apply hbase.mono' ?_ ?_
  · have hm : Measurable (quarterMomentTailIntegrand k) := by
      unfold quarterMomentTailIntegrand AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
      exact
        (measurable_const.add (measurable_const.mul (measurable_id.pow_const _))).mul
          ((measurable_id.pow_const _).mul (Real.measurable_log.pow_const k))
    exact hm.aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := (by norm_num only : (1 : ℝ) ≤ 2701).trans ht.le
    have hw : 0 ≤ target028LogMoment k t :=
      mul_nonneg (pow_nonneg (Real.log_nonneg ht1) k) (Real.rpow_nonneg (by linarith only [ht1]) _)
    have hp := Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num only : -(1 / 4 : ℝ) ≤ 0)
    have hf : 1 + (3 / 4 : ℝ) * t ^ (-(1 / 4 : ℝ)) ≤ 7 / 4 := by linarith only [hp]
    have h := mul_le_mul_of_nonneg_right hf hw
    rw [Real.norm_of_nonneg (quarter_moment_tail_integrand_nonneg k ht1)]
    simpa only [quarterMomentTailIntegrand, AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight,
      target028LogMoment, mul_comm] using h

/-- Finite tails of a Mangoldt moment converge to the total moment minus its
prefix through 2701. This transfers uniform finite estimates to the series. -/
theorem quarter_moment_tail_tendsto (k : ℕ) :
    Filter.Tendsto (fun N : ℕ ↦ ∑ n ∈ Finset.Ioc 2701 N, quarterMangoldtMoment k n) Filter.atTop
      (nhds
        ((∑' n : ℕ, quarterMangoldtMoment k n) -
          ∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n)) := by
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
  have ht := hp.sub_const (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n)
  apply Filter.Tendsto.congr' ?_ ht
  apply (Filter.eventually_ge_atTop 2701).mono
  intro N hN
  have hd : Disjoint (Finset.Ioc 0 2701) (Finset.Ioc 2701 N) :=
    Finset.disjoint_left.mpr
      (fun n hn hm ↦ (not_lt_of_ge (Finset.mem_Ioc.mp hn).2) (Finset.mem_Ioc.mp hm).1)
  have he := Finset.sum_union (f := quarterMangoldtMoment k) hd
  rw [Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hN] at he
  dsimp only
  linarith only [he]

/-- Under RH, every one of the six Mangoldt moments is bounded by its
finite prefix, the exact Chebyshev boundary correction, and an explicit
nonnegative infinite power-logarithm integral. -/
theorem quarter_moment_infinite_upper (hRH : RiemannHypothesis) {k : ℕ} (hk : k < 6) :
    (∑' n : ℕ, quarterMangoldtMoment k n) ≤
      (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n) +
        AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 *
          (2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701) +
        ∫ t in Set.Ioi (2701 : ℝ), quarterMomentTailIntegrand k t := by
  have hn :
    0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioi (2701 : ℝ))] quarterMomentTailIntegrand k := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    change (2701 : ℝ) < t at ht
    exact quarter_moment_tail_integrand_nonneg k (by linarith only [ht])
  have hlimit := quarter_moment_tail_tendsto k
  have htail :
    (∑' n : ℕ, quarterMangoldtMoment k n) - (∑ n ∈ Finset.Ioc 0 2701, quarterMangoldtMoment k n) ≤
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 *
          (2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701) +
        ∫ t in Set.Ioi (2701 : ℝ), quarterMomentTailIntegrand k t :=
    le_of_tendsto hlimit
      ((Filter.eventually_ge_atTop 2701).mono
        (fun N hN ↦ by
          have hb : (2701 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
          have hf := quarter_moment_tail_integral hRH hk hb
          simp only [Nat.floor_ofNat, Nat.floor_natCast] at hf
          change
            (∑ n ∈ Finset.Ioc 2701 N, quarterMangoldtMoment k n) ≤
              AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (79 / 50) k 2701 *
                  (2701 + (2701 : ℝ) ^ (3 / 4 : ℝ) - Chebyshev.psi 2701) +
                ∫ t in Set.Ioc (2701 : ℝ) (N : ℝ), quarterMomentTailIntegrand k t at hf
          have hi :=
            MeasureTheory.setIntegral_mono_set (quarter_moment_tail_integrable k) hn
              (Filter.Eventually.of_forall (fun t (ht : t ∈ Set.Ioc (2701 : ℝ) N) ↦ ht.1))
          linarith only [hf, hi]))
  linarith only [htail]

end PseudoPrime.PrimeTestBounds.MillerRabin
