/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevLogScaleConditions265
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailCountRH
import PseudoPrime.Analysis.NumericalLogBounds

/-! # Normalized Chebyshev bound from logarithmic height twenty-seven -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a zero-count bound through the selected cutoff and an ordinate-tail
bound at that cutoff imply the normalized psi estimate for `L ≥ 53/2`.
The logarithmic scale specializes the generic explicit formula. -/
theorem psi_error_log_scale265_tail (hRH : RiemannHypothesis) {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (2 * Real.pi * Real.exp (L / 2) / L),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hTail :
      ordinateTail (2 * Real.pi * Real.exp (L / 2) / L) ≤
        Real.log (2 * Real.pi * Real.exp (L / 2) / L) /
          (Real.pi * (2 * Real.pi * Real.exp (L / 2) / L))) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L / (2 * Real.pi) + (1 + δ / 2) * ((L / 2 - Real.log L) ^ 2 / (2 * Real.pi) + 1) +
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
  have hQ' :
    ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) (2 / δ),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        Real.log t := by
    rw [hT]
    exact hQ
  have hTail' : ordinateTail (2 / δ) ≤ Real.log (2 / δ) / (Real.pi * (2 / δ)) := by
    rw [hT]
    exact hTail
  have hb := psi_error_normalized_tail hRH (Real.exp_pos L) hc.1 hc.2.1 ht hd hd2 hwid hQ' hTail'
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

/-- Under RH and the coarse zero-count bound, the normalized psi error satisfies
the explicit logarithmic-scale estimate for `L ≥ 53/2`. The selected width and
cutoff allow the generic explicit formula to be specialized. -/
theorem psi_error_log_scale265_coarse (hRH : RiemannHypothesis) {L : ℝ} (hL : (53 / 2 : ℝ) ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L / (2 * Real.pi) + (1 + δ / 2) * ((L / 2 - Real.log L) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) / Real.pi +
        3 / Real.exp (L / 2) := by
  have hc := scale265_conditions hL
  have hbase : 2 * Real.pi * Real.exp 1 ≤ (1000 : ℝ) := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp]
  apply psi_error_log_scale265_tail hRH hL
  · intro t ht
    exact hQ t ht.1
  · apply ordinateTail_of_coarse_count hRH hc.2.2
    intro t ht
    exact hQ t (le_trans hbase (le_trans hc.2.2 ht))

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
