/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundNormalizedPhase
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Numerical budget for the normalized Backlund phase -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `T ≥ 17`, the explicit normalized Backlund phase budget is at most
`(3/8) log T + 8/5`. Rational bounds for `π`, `log 2`, `log(14/5)` and the
positive reciprocal terms reduce the comparison to arithmetic. -/
theorem backlund_phase_budget_le {T : ℝ} (hT : 17 ≤ T) :
    Real.log (14 / 5) / Real.pi +
        ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        ((1 / T) / Real.pi) / 2 ≤
      (3 / 8 : ℝ) * Real.log T + 8 / 5 := by
  have hZ : Real.log (14 / 5 : ℝ) ≤ 21 / 20 := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).2
    have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have hf := Real.add_one_le_exp (1 / 20 : ℝ)
    have hm := mul_le_mul he hf (by norm_num only : (0 : ℝ) ≤ 1 / 20 + 1) (Real.exp_pos 1).le
    have heq : (21 / 20 : ℝ) = 1 + 1 / 20 := by norm_num only
    rw [heq, Real.exp_add]
    nlinarith only [hm]
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hL : (69 / 100 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith only [hT])
  have h15 : (15 : ℝ) ≤ T - 2 := by linarith only [hT]
  have hsq : (225 : ℝ) ≤ (T - 2) ^ 2 := by nlinarith only [h15]
  have hinv : 1 / (T - 2) ^ 2 ≤ (1 / 225 : ℝ) := one_div_le_one_div_of_le (by norm_num only) hsq
  have hterm1 : Real.log (14 / 5 : ℝ) / Real.pi ≤ 7 / 20 := by
    apply (div_le_iff₀ Real.pi_pos).2
    nlinarith only [hZ, hp]
  let M : ℝ := 63 / 40 + (1 / 2) * Real.log T + 1 / 75
  have hM0 : 0 ≤ M := by
    dsimp only [M]; linarith only [hlogT]
  have hK : (3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2 ≤ M := by
    dsimp only [M]
    have he : (3 : ℝ) / (T - 2) ^ 2 = 3 * (1 / (T - 2) ^ 2) := by ring
    rw [he]
    nlinarith only [hZ, hinv]
  have hden : (69 / 50 : ℝ) ≤ 2 * Real.log 2 := by linarith only [hL]
  have hdenpos : 0 < 2 * Real.log 2 := by linarith only [hden]
  have hterm2 :
    ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
        (2 * Real.log 2) ≤
      (50 / 69 : ℝ) * M := by
    apply (div_le_iff₀ hdenpos).2
    have hm := mul_nonneg (sub_nonneg.mpr hden) hM0
    nlinarith only [hK, hm]
  have htinv : 1 / T ≤ (1 / 17 : ℝ) := one_div_le_one_div_of_le (by norm_num only) hT
  have hpinv : 1 / Real.pi ≤ (1 / 3 : ℝ) := one_div_le_one_div_of_le (by norm_num only) hp
  have hmul :=
    mul_le_mul htinv hpinv (one_div_nonneg.mpr Real.pi_pos.le) (by norm_num only : (0 : ℝ) ≤ 1 / 17)
  have hterm3 : ((1 / T) / Real.pi) / 2 ≤ (1 / 102 : ℝ) := by
    have he : ((1 / T) / Real.pi) / 2 = ((1 / T) * (1 / Real.pi)) / 2 := by ring
    rw [he]
    nlinarith only [hmul]
  dsimp only [M] at hterm2
  nlinarith only [hterm1, hterm2, hterm3, hlogT]

/-- At every good height at least `17`, an Euler-normalized continuous zeta
argument satisfies `|φ(1/2)|/π ≤ (3/8) log T + 8/5`. This combines the
analytic Backlund estimate with the explicit numerical budget. -/
theorem exists_euler_arg_coarse {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
        (∀ x : ℝ,
          x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
            riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
              (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        φ (3 / 2) =
          (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
              (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im ∧
        |φ (1 / 2)| / Real.pi ≤ (3 / 8 : ℝ) * Real.log T + 8 / 5 := by
  obtain ⟨φ, hc, hp, hn, hb⟩ := exists_euler_arg_bound hT hgood
  exact ⟨φ, hc, hp, hn, hb.trans (backlund_phase_budget_le hT)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
