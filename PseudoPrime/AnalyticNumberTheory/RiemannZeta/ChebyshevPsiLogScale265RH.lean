/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiScaledSharpRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions265
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Improved Chebyshev bound from logarithmic height twenty-six and one half -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and `L ≥ 53/2`, the normalized Chebyshev error satisfies the
displayed logarithmic bound with the refined low-zero constant `13/20`.
The chosen width and cutoff specialize the normalized zero-split estimate. -/
theorem psi_error_log_scale265_065 (hRH : RiemannHypothesis) {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L / (2 * Real.pi) + (1 + δ / 2) * ((L / 2 - Real.log L) ^ 2 / (2 * Real.pi) + 13 / 20) +
        (1 + δ) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) / Real.pi +
        3 / Real.exp (L / 2) := by
  dsimp only
  let δ := L / (Real.pi * Real.exp (L / 2))
  let h := Real.exp (L / 2) * L / Real.pi
  have hi := scale265_identities hL
  change
    0 < δ ∧
      δ ≤ 1 / 2 ∧
      1 ≤ h ∧
      h = Real.exp L * δ ∧
      2 / δ = 2 * Real.pi * Real.exp (L / 2) / L ∧
      Real.log ((2 / δ) / (2 * Real.pi)) = L / 2 - Real.log L ∧
      Real.log (2 / δ) = L / 2 - Real.log L + Real.log (2 * Real.pi) at hi
  obtain ⟨hd, hd2, hw1, hwid, hT, hlog1, hlog2⟩ := hi
  have hc := scale265_conditions hL
  change 0 < h ∧ 1 < Real.exp L - h ∧ 1000 ≤ 2 * Real.pi * Real.exp (L / 2) / L at hc
  have ht : 1000 ≤ 2 / δ := by
    rw [hT]
    exact hc.2.2
  have hb := psi_error_normalized_065 hRH (Real.exp_pos L) hc.1 hc.2.1 ht hd hd2 hwid
  rw [hlog1, hlog2] at hb
  have he : 0 < Real.exp (L / 2) := Real.exp_pos _
  have hs : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    have heq : Real.exp L = Real.exp (L / 2) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [heq, Real.sqrt_sq_eq_abs, abs_of_pos he]
  rw [hs] at hb
  have hh : h / (2 * Real.exp (L / 2)) = L / (2 * Real.pi) := by
    dsimp only [h]
    have he0 : Real.exp (L / 2) ≠ 0 := he.ne'
    rw [div_div, show Real.pi * (2 * Real.exp (L / 2)) = Real.exp (L / 2) * (2 * Real.pi) by ring]
    exact mul_div_mul_left L (2 * Real.pi) he0
  rw [hh] at hb
  have hconst : Real.log (2 * Real.pi) + 1 / h ≤ 3 := by
    have hinv : 1 / h ≤ 1 := (div_le_one₀ (lt_of_lt_of_le (by norm_num only) hw1)).2 hw1
    have hp := Analysis.log_two_mul_pi_lt
    norm_num only at hp
    linarith only [hinv, hp]
  have hconst' := div_le_div_of_nonneg_right hconst he.le
  have heq :
    (Real.log (2 * Real.pi) + 1 / h) / Real.exp (L / 2) =
      Real.log (2 * Real.pi) / Real.exp (L / 2) + 1 / (h * Real.exp (L / 2)) := by
    rw [add_div, div_div]
  rw [heq] at hconst'
  exact le_trans hb (by linarith only [hconst'])

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
