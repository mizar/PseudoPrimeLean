/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedLogExplicit
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Integrating the logarithmic zero series

Uniform convergence and finite-ledger integration on positive compact intervals.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- On an interval starting at least at one, the finite partial sums of the
nontrivial logarithmic zero terms converge uniformly. The endpoint `b` times
the inverse-square zero mass gives a summable majorant. -/
theorem zero_uniform {a b : ℝ} (ha : 1 ≤ a) :
    TendstoUniformlyOn (fun s : Finset ℂ ↦ fun x : ℝ ↦ ∑ ρ ∈ s, nontrivialLogZeroTerm x ρ)
      (fun x : ℝ ↦ ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ) Filter.atTop (Set.Icc a b) := by
  have hs := (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left b
  apply tendstoUniformlyOn_tsum hs
  intro ρ x hx
  exact
    (norm_nontrivialLogZeroTerm_le (ha.trans hx.1) ρ).trans
      (mul_le_mul_of_nonneg_right hx.2 (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ))

/-- Each logarithmic zero term is continuous on a strictly positive closed
interval. When it is nonzero, continuity follows from the complex power. -/
theorem zero_term_continuous {a b : ℝ} (ha : 0 < a) (ρ : ℂ) :
    ContinuousOn (fun x : ℝ ↦ nontrivialLogZeroTerm x ρ) (Set.Icc a b) := by
  by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
  · simp only [nontrivialLogZeroTerm, h, riemannZetaLogZeroContribution]
    intro x hx
    exact
      (((Complex.continuousAt_ofReal_cpow_const x ρ
                  (Or.inr (ne_of_gt (lt_of_lt_of_le ha hx.1)))).const_mul
              _).div_const
          _).continuousWithinAt
  · simp only [nontrivialLogZeroTerm, h, ↓reduceIte]
    exact continuousOn_const

/-- The logarithmic nontrivial-zero sum is continuous on a closed interval
starting at least at one. Apply the uniform majorant to the continuous terms. -/
theorem zero_sum_continuous {a b : ℝ} (ha : 1 ≤ a) :
    ContinuousOn (fun x : ℝ ↦ ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ) (Set.Icc a b) := by
  have hs := (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left b
  apply continuousOn_tsum (fun ρ ↦ zero_term_continuous (zero_lt_one.trans_le ha) ρ) hs
  intro ρ x hx
  exact
    (norm_nontrivialLogZeroTerm_le (ha.trans hx.1) ρ).trans
      (mul_le_mul_of_nonneg_right hx.2 (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ))

/-- The logarithmic nontrivial-zero sum is interval integrable on ordered
endpoints at least one, by continuity of its uniformly convergent series. -/
theorem zero_sum_integrable {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ ↦ ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ) MeasureTheory.volume a
      b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact zero_sum_continuous ha

/-- On `1 ≤ a ≤ b`, the sums of the integrals over the expanding finite
zero ledgers converge to the integral of the full nontrivial-zero sum. The
inverse-square mass bounds the finite sums for dominated convergence. -/
theorem zero_integrals_limit {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Filter.Tendsto
      (fun m : ℕ ↦
        ∑
          ρ ∈
            (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0),
          ∫ x in a..b, nontrivialLogZeroTerm x ρ)
      Filter.atTop (nhds (∫ x in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
  classical
  let S : ℕ → Finset ℂ := fun m ↦
    (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)).filter
      (fun ρ ↦ ¬ρ.re < 0)
  let F : ℕ → ℝ → ℂ := fun m x ↦ ∑ ρ ∈ S m, nontrivialLogZeroTerm x ρ
  let bound : ℝ := ∑' ρ : ℂ, b * RiemannXi.inversePowerZeroWeight 2 ρ
  have hs := (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left b
  have hterm (m : ℕ) : ContinuousOn (F m) (Set.Icc a b) := by
    exact continuousOn_finsetSum (S m) (fun ρ _ ↦ zero_term_continuous (zero_lt_one.trans_le ha) ρ)
  have hlim :
    Filter.Tendsto (fun m ↦ ∫ x in a..b, F m x) Filter.atTop
      (nhds (∫ x in a..b, ∑' ρ : ℂ, nontrivialLogZeroTerm x ρ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ bound)
    · filter_upwards with m
      apply ContinuousOn.aestronglyMeasurable
      · exact
          (hterm m).mono
            (by
              rw [Set.uIoc_of_le hab]
              exact Set.Ioc_subset_Icc_self)
      · exact measurableSet_uIoc
    · filter_upwards with m
      filter_upwards with x hx
      have hx' : x ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩
      calc
        ‖F m x‖ ≤ ∑ ρ ∈ S m, ‖nontrivialLogZeroTerm x ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ S m, b * RiemannXi.inversePowerZeroWeight 2 ρ := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact
            (norm_nontrivialLogZeroTerm_le (ha.trans hx'.1) ρ).trans
              (mul_le_mul_of_nonneg_right hx'.2 (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ))
        _ ≤ bound :=
          hs.sum_le_tsum _
            (fun ρ _ ↦
              mul_nonneg (zero_le_one.trans (ha.trans hab))
                (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ))
    · exact intervalIntegrable_const
    · filter_upwards with x hx
      have hx' : x ∈ Set.Icc a b := by
        rw [Set.uIoc_of_le hab] at hx
        exact ⟨hx.1.le, hx.2⟩
      rw [Set.uIoc_of_le hab] at hx
      have hh := log_zero_tsum_limit (lt_of_le_of_lt ha hx.1)
      apply hh.congr'
      filter_upwards with m
      apply Finset.sum_congr rfl
      intro ρ hρ
      have hmem := Finset.mem_filter.mp hρ
      have hz := (mem_riemannZetaZerosInAnyRectangle_iff.mp hmem.1).2
      simp only [nontrivialLogZeroTerm, hz, true_and, not_lt.mp hmem.2, ↓reduceIte]
  apply hlim.congr'
  filter_upwards with m
  rw [intervalIntegral.integral_finsetSum]
  intro ρ hρ
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact zero_term_continuous (zero_lt_one.trans_le ha) ρ

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
