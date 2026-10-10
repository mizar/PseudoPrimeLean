/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.LogarithmicShiftIntegral
public import Mathlib.NumberTheory.LSeries.Injectivity
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Exponential decay and half-line integrability of Dirichlet series with no constant term.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For coefficients vanishing at zero and one with finite abscissa of absolute convergence,
the real-axis L-series is O(2^(-sigma)). The scaled series tends to its coefficient at two,
so division by the nonzero exponential yields the bound. -/
theorem isBigO_LSeries_of_zero_one (a : ℕ → ℂ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤) :
    Asymptotics.IsBigO Filter.atTop (fun σ : ℝ ↦ LSeries a (σ : ℂ))
      (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) := by
  have hzero : ∀ m ≤ 1, a m = 0 := by
    intro m hm
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · exact ha0
    · exact ha1
  have hlim := LSeries.tendsto_cpow_mul_atTop hzero ha
  have hbound := hlim.norm.eventually_lt_const (lt_add_one ‖a 2‖)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨‖a 2‖ + 1, ?_⟩
  filter_upwards [hbound] with σ hσ
  have hp : (2 : ℂ) ^ (σ : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num only))
  have hpos : 0 < ‖(2 : ℂ) ^ (σ : ℂ)‖ := norm_pos_iff.mpr hp
  have hσ' : ‖(2 : ℂ) ^ (σ : ℂ)‖ * ‖LSeries a (σ : ℂ)‖ ≤ ‖a 2‖ + 1 := by
    simpa only [Nat.cast_one, show (1 : ℂ) + 1 = 2 by norm_num only, norm_mul] using hσ.le
  rw [Complex.cpow_neg, norm_inv, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using hσ')

/-- A complex function continuous on sigma>=1 and eventually equal to an L-series with
vanishing coefficients at zero and one is integrable over sigma>1, if that series has finite
abscissa of absolute convergence. Combine local integrability with exponential decay. -/
theorem integrableOn_of_eventuallyEq_LSeries_zero_one (a : ℕ → ℂ) (ha0 : a 0 = 0) (ha1 : a 1 = 0)
    (ha : LSeries.abscissaOfAbsConv a < ⊤) {F : ℝ → ℂ} (hF : ContinuousOn F (Set.Ici 1))
    (heq : Filter.EventuallyEq Filter.atTop (fun σ : ℝ ↦ LSeries a (σ : ℂ)) F) :
    MeasureTheory.IntegrableOn F (Set.Ioi 1) := by
  have ho := (isBigO_LSeries_of_zero_one a ha0 ha1 ha).congr' heq (Filter.EventuallyEq.rfl)
  have hg : MeasureTheory.IntegrableAtFilter (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) Filter.atTop :=
    ⟨Set.Ioi 1, Filter.Ioi_mem_atTop 1, integrableOn_cpow_neg_real (by norm_num only)⟩
  have hi := (hF.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop ho hg
  exact hi.mono_set Set.Ioi_subset_Ici_self

/-- A complex-valued function continuous on `[1,∞)` and bounded by `O(2^(-σ))` at
positive real infinity is integrable on `(1,∞)`. Combine integrability on bounded intervals
with the integrable exponential tail. This discharges endpoint integral hypotheses from
real-axis decay estimates. -/
theorem integrableOn_of_isBigO_two_neg_cpow {F : ℝ → ℂ} (hF : ContinuousOn F (Set.Ici 1))
    (ho : Asymptotics.IsBigO Filter.atTop F (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ)))) :
    MeasureTheory.IntegrableOn F (Set.Ioi 1) := by
  have hg : MeasureTheory.IntegrableAtFilter (fun σ : ℝ ↦ (2 : ℂ) ^ (-(σ : ℂ))) Filter.atTop :=
    ⟨Set.Ioi 1, Filter.Ioi_mem_atTop 1, integrableOn_cpow_neg_real (by norm_num only)⟩
  have hi := (hF.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop ho hg
  exact hi.mono_set Set.Ioi_subset_Ici_self

end PseudoPrime.AnalyticNumberTheory.General
