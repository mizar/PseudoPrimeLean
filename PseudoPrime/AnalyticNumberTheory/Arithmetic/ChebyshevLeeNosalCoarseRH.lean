/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevScaleError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiLogScaleCoarseRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevGap43
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevPrimePowers

/-! # Lee–Nosal high-range bounds from coarse zero counting -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Under RH and the stated coarse zero-count bound, the normalized
Chebyshev error satisfies the explicit logarithmic-scale estimate for
`L ≥ 43`. The last term absorbs the constant and inverse-width terms. -/
theorem psi_error_log_scale_coarse (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      L / (2 * Real.pi) + (1 + δ / 2) * ((L / 2 - Real.log L) ^ 2 / (2 * Real.pi) + 1) +
        (1 + δ) * (L / 2 - Real.log L + Real.log (2 * Real.pi)) / Real.pi +
        3 / Real.exp (L / 2) := by
  exact RiemannZeta.psi_error_log_scale265_coarse hRH (by linarith only [hL]) hQ

/-- Under RH and the stated coarse zero-count hypothesis, split the
normalized logarithmic-scale Chebyshev bound into its main expression and
the explicit exponentially small remainder. -/
theorem psi_error_main_remainder_coarse (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    let a := L / 2 - Real.log L
    let c := Real.log (2 * Real.pi)
    let δ := L / (Real.pi * Real.exp (L / 2))
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      (a ^ 2 + 2 * a + 2 * c + L) / (2 * Real.pi) + 1 +
        (δ * a ^ 2 / (4 * Real.pi) + δ / 2 + δ * (a + c) / Real.pi + 3 / Real.exp (L / 2)) := by
  dsimp only
  have h := psi_error_log_scale_coarse hRH hL hQ
  dsimp only at h
  convert h using 1
  ring

/-- Under RH and the stated coarse positive zero-count estimate, the
normalized Chebyshev error for `L ≥ 43` is bounded by the explicit main
term plus `101/100`. The count estimate remains an assumption. -/
theorem psi_error_main_43_coarse (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| / Real.exp (L / 2) ≤
      ((L / 2 - Real.log L) ^ 2 + 2 * (L / 2 - Real.log L) + 2 * Real.log (2 * Real.pi) + L) /
          (2 * Real.pi) +
        101 / 100 := by
  have hm := psi_error_main_remainder_coarse hRH hL hQ
  have hr := RiemannZeta.scale43_remainder_le hL
  dsimp only at hm hr
  linarith only [hm, hr]

/-- Under RH and the stated coarse positive-height zero-count bound,
the Chebyshev error at `exp L`, for `L ≥ 43`, lies below the target envelope
with an additional `11/4` times the square-root scale of margin. The count
estimate remains an explicit hypothesis. -/
theorem psi_error_envelope43_coarse (hRH : RiemannHypothesis) {L : ℝ} (hL : 43 ≤ L)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    |Chebyshev.psi (Real.exp L) - Real.exp L| ≤
      Real.exp (L / 2) * (L * (L - Real.log L) / (8 * Real.pi) - 11 / 4) := by
  have h := (psi_error_main_43_coarse hRH hL hQ).trans (RiemannZeta.chebyshev_main_le_envelope hL)
  have hp := Real.exp_pos (L / 2)
  have hm := (div_le_iff₀ hp).1 h
  nlinarith only [hm]

/-- Under RH and the stated coarse zero-count hypothesis, for positive
`x` with `log x ≥ 43`, the Chebyshev error lies below the target envelope
minus `11/4` times `sqrt x`. Substitute `L = log x` in the scale theorem. -/
theorem psi_error_envelope_of_log_coarse (hRH : RiemannHypothesis) {x : ℝ} (hx : 0 < x)
    (hL : 43 ≤ Real.log x)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |RiemannZeta.positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    |Chebyshev.psi x - x| ≤
      Real.sqrt x *
        (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) - 11 / 4) := by
  have h := psi_error_envelope43_coarse hRH hL hQ
  have hs : Real.exp (Real.log x / 2) = Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [Real.exp_log hx, hs] at h
  exact h

end PseudoPrime.AnalyticNumberTheory.Arithmetic
