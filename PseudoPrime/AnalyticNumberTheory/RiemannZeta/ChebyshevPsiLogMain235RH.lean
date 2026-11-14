/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiNormalizedBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions235

/-! # Sharp Chebyshev main term and remainder at logarithmic scale 23.5 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Substituting the cutoff `2 / δ` into the sharp tail budget gives the
polynomial remainder displayed on the right. The relative width `δ` is nonzero. -/
private theorem tail_eq {δ a B : ℝ} (hd : δ ≠ 0) :
    (2 * (1 + δ) / δ) * ((a + 1) / (Real.pi * (2 / δ)) + B / (2 / δ) ^ 2 + 2 / (3 * (2 / δ) ^ 3)) =
      (1 + δ) * ((a + 1) / Real.pi + δ * B / 2 + δ ^ 2 / 6) := by
  have hc := mul_inv_cancel₀ hd
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv, mul_pow]
  linear_combination ((1 + δ) * ((a + 1) / Real.pi + δ * B / 2 + δ ^ 2 / 6)) * hc

/-- Under RH and `L ≥ 47/2`, the selected smoothing width yields the displayed
main term and explicit remainder for the normalized Chebyshev psi error.
The proof substitutes the sharp tail before collecting the main and error terms. -/
theorem psi_error_main_remainder235 (hRH : RiemannHypothesis) {L : ℝ} (hL : (47 / 2 : ℝ) ≤ L) :
    let δ := 5 * L / (6 * Real.pi * Real.exp (L / 2))
    let h := (5 * L / (6 * Real.pi)) * Real.exp (L / 2)
    let a := L / 2 - Real.log (5 * L / 6)
    let c := Real.log (2 * Real.pi)
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      (a ^ 2 + 2 * a + 2 + 5 * L / 6) / (2 * Real.pi) + 53 / 100 +
        (δ * a ^ 2 / (4 * Real.pi) + 53 / 100 * δ / 2 + δ * (a + 1) / Real.pi +
          δ * (1 + δ) / 2 * ((3 / 2 : ℝ) * (a + c) + 271 / 40) +
          δ ^ 2 * (1 + δ) / 6 +
          c / Real.exp (L / 2) +
          1 / (h * Real.exp (L / 2))) := by
  dsimp only
  let δ := 5 * L / (6 * Real.pi * Real.exp (L / 2))
  let h := (5 * L / (6 * Real.pi)) * Real.exp (L / 2)
  let a := L / 2 - Real.log (5 * L / 6)
  let c := Real.log (2 * Real.pi)
  change
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      (a ^ 2 + 2 * a + 2 + 5 * L / 6) / (2 * Real.pi) + 53 / 100 +
        (δ * a ^ 2 / (4 * Real.pi) + 53 / 100 * δ / 2 + δ * (a + 1) / Real.pi +
          δ * (1 + δ) / 2 * ((3 / 2 : ℝ) * (a + c) + 271 / 40) +
          δ ^ 2 * (1 + δ) / 6 +
          c / Real.exp (L / 2) +
          1 / (h * Real.exp (L / 2)))
  have hi := scale235_identities hL
  change
    0 < δ ∧
      δ ≤ 1 / 1000 ∧
      h = Real.exp L * δ ∧
      2 / δ = 12 * Real.pi * Real.exp (L / 2) / (5 * L) ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = a at hi
  have hc := scale235_conditions hL
  change
    0 < δ ∧
      δ ≤ 1 / 1000 ∧
      0 < h ∧ 1 < Real.exp L - h ∧ 2000 ≤ 12 * Real.pi * Real.exp (L / 2) / (5 * L) at hc
  have ht : 1000 ≤ 2 / δ := by
    rw [hi.2.2.2.1]
    linarith only [hc.2.2.2.2]
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (1000 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  have hd2 : δ ≤ 1 / 2 := by linarith only [hi.2.1]
  have hb :=
    psi_error_normalized_budget_of_RH hRH (hbase.trans ht) (Real.exp_pos L) hc.2.2.1 hc.2.2.2.1
      hi.1.le hd2 hi.2.2.1
  have ht0 : (2 / δ : ℝ) ≠ 0 := ne_of_gt (div_pos (by norm_num only) hi.1)
  have hp0 : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have hlog : Real.log (2 / δ) = a + c := by
    have hl := hi.2.2.2.2
    rw [Real.log_div ht0 hp0] at hl
    change Real.log (2 / δ) - c = a at hl
    linarith only [hl]
  rw [hi.2.2.2.2, hlog] at hb
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hs : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have heq : Real.exp L = Real.exp (L / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos he]
  rw [hs] at hb
  have hw : h / (2 * Real.exp (L / 2)) = (5 * L / (6 * Real.pi)) / 2 := by
    dsimp only [h]
    have heq := mul_inv_cancel₀ he.ne'
    simp only [div_eq_mul_inv, mul_inv_rev] at heq ⊢
    linear_combination (5 * L / (6 * Real.pi) / 2) * heq
  rw [hw] at hb
  rw [tail_eq hi.1.ne'] at hb
  convert hb using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
