/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Order-at-most-one growth and global exponential bounds
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A growth condition on `F : ℂ → ℂ`: for each real `r > 1`, some positive `A` and
nonnegative radius `R` bound `‖F s‖` by `exp(A * ‖s‖^r)` whenever `R ≤ ‖s‖`.
Analyticity is a separate premise. For entire functions this provides the order-at-most-one
growth used in Jensen zero counts and the genus-one Hadamard expansion. -/
def HasOrderAtMostOne (F : ℂ → ℂ) : Prop :=
  ∀ r : ℝ, 1 < r → ∃ A R : ℝ, 0 < A ∧ 0 ≤ R ∧ ∀ s : ℂ, R ≤ ‖s‖ → ‖F s‖ ≤ Real.exp (A * ‖s‖ ^ r)

/-- A continuous function of order at most one admits a global exponential
power bound for every exponent greater than one. Absorb the compact inner ball's
bound into the growth constant. This permits Jensen estimates at every radius. -/
theorem exists_global_exponential_bound_of_orderAtMostOne {F : ℂ → ℂ} (hF : Continuous F)
    (horder : HasOrderAtMostOne F) {r : ℝ} (hr : 1 < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r) := by
  obtain ⟨A, R, hA, hR, hg⟩ := horder r hr
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (x := (0 : ℂ)) (r := R)).bddAbove_image hF.norm.continuousOn
  let C : ℝ := max A (max 1 M)
  have hC : 0 < C := hA.trans_le (le_max_left _ _)
  refine ⟨C, hC, fun z ↦ ?_⟩
  have hp : 1 ≤ (‖z‖ + 1) ^ r :=
    Real.one_le_rpow (by linarith only [norm_nonneg z]) (zero_lt_one.trans hr).le
  by_cases hz : R ≤ ‖z‖
  · refine (hg z hz).trans (Real.exp_le_exp.mpr ?_)
    exact
      mul_le_mul (le_max_left A (max 1 M))
        (Real.rpow_le_rpow (norm_nonneg z) (le_add_of_nonneg_right zero_le_one)
          (zero_lt_one.trans hr).le)
        (Real.rpow_nonneg (norm_nonneg z) _) hC.le
  · have hm : ‖F z‖ ≤ M :=
      hM
        ⟨z, by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (lt_of_not_ge hz).le, rfl⟩
    calc
      ‖F z‖ ≤ M := hm
      _ ≤ C := (le_max_right 1 M).trans (le_max_right A (max 1 M))
      _ ≤ C * (‖z‖ + 1) ^ r := le_mul_of_one_le_right hC.le hp
      _ ≤ _ := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)

/-- For every r > 1, (t+3) log(t+3) is eventually bounded by 4^r t^r with t at least one.
Use log t = o(t^(r-1)), then compare t+3 with 4t.
This turns the available logarithmic growth envelope into an order-at-most-one bound. -/
private theorem eventually_shifted_mul_log_le_rpow {r : ℝ} (hr : 1 < r) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ t : ℝ, R ≤ t → (t + 3) * Real.log (t + 3) ≤ (4 : ℝ) ^ r * t ^ r := by
  have hpos : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨R₀, hR₀⟩ :=
    Filter.eventually_atTop.mp
      ((isLittleO_log_rpow_atTop hpos).bound (show (0 : ℝ) < 1 from zero_lt_one))
  refine ⟨max 1 R₀, le_max_left _ _, ?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 < t := zero_lt_one.trans_le ht1
  have ht3 : 0 < t + 3 := by linarith only [ht0]
  have hlog := hR₀ (t + 3) (by linarith only [le_max_right 1 R₀, ht])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by linarith only [ht1])),
    abs_of_nonneg (Real.rpow_nonneg ht3.le _), one_mul] at hlog
  have hpow : (t + 3) * (t + 3) ^ (r - 1) = (t + 3) ^ r := by
    have he := Real.rpow_add ht3 1 (r - 1)
    rw [Real.rpow_one, show (1 : ℝ) + (r - 1) = r from by ring] at he
    exact he.symm
  calc
    (t + 3) * Real.log (t + 3) ≤ (t + 3) * (t + 3) ^ (r - 1) :=
      mul_le_mul_of_nonneg_left hlog ht3.le
    _ = (t + 3) ^ r := hpow
    _ ≤ (4 * t) ^ r := Real.rpow_le_rpow ht3.le (by linarith only [ht1]) (zero_lt_one.trans hr).le
    _ = (4 : ℝ) ^ r * t ^ r := Real.mul_rpow (by norm_num only) ht0.le

/-- For any complex function and positive `C`, a bound
`‖F s‖ ≤ exp(C * (‖s‖ + 3) * log(‖s‖ + 3))` for `‖s‖ ≥ 1` implies
`HasOrderAtMostOne F`. For each `r > 1`, compare the logarithmic growth with `4^r * ‖s‖^r`
beyond a suitable radius. This derives the order condition for normalized completions
without requiring analyticity in this comparison lemma. -/
theorem hasOrderAtMostOne_of_exp_norm_mul_log_bound (F : ℂ → ℂ) {C : ℝ} (hC : 0 < C)
    (hb : ∀ s : ℂ, 1 ≤ ‖s‖ → ‖F s‖ ≤ Real.exp (C * ((‖s‖ + 3) * Real.log (‖s‖ + 3)))) :
    HasOrderAtMostOne F := by
  intro r hr
  obtain ⟨R, hR, hbound⟩ := eventually_shifted_mul_log_le_rpow hr
  refine
    ⟨C * (4 : ℝ) ^ r, R, mul_pos hC (Real.rpow_pos_of_pos (by norm_num only) _),
      zero_le_one.trans hR, ?_⟩
  intro s hs
  exact
    (hb s (hR.trans hs)).trans
      (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left (hbound ‖s‖ hs) hC.le]))

end PseudoPrime.AnalyticNumberTheory.General
