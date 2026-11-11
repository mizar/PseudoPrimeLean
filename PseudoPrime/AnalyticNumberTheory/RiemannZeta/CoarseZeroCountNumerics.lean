/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountRightLimit
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Coarse zero-count budget at good heights -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Above `2πe`, the proposed good-height error budget is bounded by
`log t`. Explicit bounds for `π`, `e` and `log 2` control the endpoint. -/
theorem good_count_budget_le_log {t : ℝ} (ht : 2 * Real.pi * Real.exp 1 ≤ t) :
    (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t) ≤ Real.log t := by
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have he : (163 / 60 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hpe := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 163 / 60) Real.pi_pos.le
  have ht17 : (17 : ℝ) ≤ t := by nlinarith only [hpe, ht]
  have hlog16 := Real.log_le_log (by norm_num only : (0 : ℝ) < 16) (by linarith only [ht17])
  have heq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num only at h ⊢
    exact h
  rw [heq] at hlog16
  have hinv := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 17) ht17
  have heq' : 1 / (5 * t) = (1 / 5 : ℝ) * (1 / t) := by ring
  rw [heq']
  nlinarith only [hlog16, Real.log_two_gt_d9, hinv]

/-- A good-height zero-count estimate with the displayed `3/8` budget implies
the coarse logarithmic estimate at every height at least `2πe`. Apply the
numeric budget and the right-limit transfer for the closed-height count. -/
theorem positiveZeroCount_log_of_good_budget
    (hgood :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          |positiveZeroCount t -
                (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
            (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t)) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
  apply positiveZeroCount_log_of_good
  intro t ht hzero
  exact (hgood t ht hzero).trans (good_count_budget_le_log ht)

/-- If the good-height counting error splits into an argument term and a
Gamma-phase term with the displayed bounds, the coarse count follows at all
heights. The identity and both phase bounds remain explicit hypotheses. -/
theorem positiveZeroCount_log_of_phases {S E : ℝ → ℝ}
    (hid :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8) =
            S t + E t)
    (hS :
      ∀ t : ℝ,
        2 * Real.pi * Real.exp 1 ≤ t →
          (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
          |S t| ≤ (3 / 8 : ℝ) * Real.log t + 8 / 5)
    (hE : ∀ t : ℝ, 2 * Real.pi * Real.exp 1 ≤ t → |E t| ≤ 1 / (5 * t)) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
  apply positiveZeroCount_log_of_good_budget
  intro t ht hz
  rw [hid t ht hz]
  calc
    |S t + E t| ≤ |S t| + |E t| := abs_add_le _ _
    _ ≤ (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t) := add_le_add (hS t ht hz) (hE t ht)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
