/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting

/-! # Finite approximations to the ordinate tail -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, the finite inverse-square sum over zeros of height in `(T, U]`
converges to the ordinate tail as `U` tends to infinity. Every nontrivial zero
eventually occurs in the finite ledger, and the Xi inverse-square mass provides
a summable dominating family. This connects height-counting estimates with the
tail hypothesis in the Chebyshev bound. -/
theorem ordinateTail_limit (hRH : RiemannHypothesis) (T : ℝ) :
    Filter.Tendsto
      (fun U : ℝ ↦
        ∑ ρ ∈ (zerosUpTo U).filter (fun ρ ↦ T < |ρ.im|),
          (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2)
      Filter.atTop (nhds (ordinateTail T)) := by
  classical
  let f : ℝ → ℂ → ℝ := fun U ρ ↦ if ρ ∈ zerosUpTo U then ordinateTailWeight T ρ else 0
  have hpoint (ρ : ℂ) :
    Filter.Tendsto (fun U ↦ f U ρ) Filter.atTop (nhds (ordinateTailWeight T ρ)) := by
    by_cases h : riemannZeta ρ = 0 ∧ 0 ≤ ρ.re
    · have hm : ∀ᶠ U : ℝ in Filter.atTop, ρ ∈ zerosUpTo U := by
        filter_upwards [Filter.eventually_ge_atTop (max 0 |ρ.im|)] with U hU
        exact (mem_zerosUpTo ((le_max_left _ _).trans hU)).2 ⟨h.1, h.2, (le_max_right _ _).trans hU⟩
      apply tendsto_const_nhds.congr'
      filter_upwards [hm] with U hU
      simp only [f, hU, ↓reduceIte]
    · have hz : ordinateTailWeight T ρ = 0 := by
        have hn : ¬(riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ T < |ρ.im|) := fun hh ↦ h ⟨hh.1, hh.2.1⟩
        simp only [ordinateTailWeight_eq, hn, ↓reduceIte]
      simp only [f, hz, ite_self]
      exact tendsto_const_nhds
  have hbound :
    ∀ᶠ U : ℝ in Filter.atTop, ∀ ρ : ℂ, ‖f U ρ‖ ≤ 2 * RiemannXi.inversePowerZeroWeight 2 ρ := by
    filter_upwards with U ρ
    by_cases hm : ρ ∈ zerosUpTo U
    · simpa only [f, hm, ↓reduceIte, Real.norm_eq_abs,
        abs_of_nonneg (ordinateTailWeight_bound hRH T ρ).1] using
        (ordinateTailWeight_bound hRH T ρ).2
    · simp only [f, hm, ↓reduceIte, norm_zero]
      exact mul_nonneg (by norm_num only) (RiemannXi.inversePowerZeroWeight_nonneg 2 ρ)
  have hs := (RiemannXi.summable_inversePowerZeroWeight (by norm_num only : (1 : ℝ) < 2)).mul_left 2
  have hlim := tendsto_tsum_of_dominated_convergence hs hpoint hbound
  rw [ordinateTail_eq]
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with U hU
  rw [tsum_eq_sum (s := zerosUpTo U) (fun ρ hρ ↦ by simp only [f, hρ, ↓reduceIte])]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hz := (mem_zerosUpTo hU).1 hρ
  simp only [f, hρ, ↓reduceIte, ordinateTailWeight_eq, hz.1, hz.2.1, true_and]

/-- Under RH, an eventual uniform bound for the finite height tails bounds the
full ordinate tail. Pass the inequality to the limit of the finite sums. -/
theorem ordinateTail_le_of_eventually (hRH : RiemannHypothesis) (T C : ℝ)
    (h :
      ∀ᶠ U : ℝ in Filter.atTop,
        (∑ ρ ∈ (zerosUpTo U).filter (fun ρ ↦ T < |ρ.im|),
            (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) ≤
          C) :
    ordinateTail T ≤ C := by exact le_of_tendsto (ordinateTail_limit hRH T) h

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
