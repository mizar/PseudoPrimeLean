/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonZeroSum
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFiveHalvesBound
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EulerFiveHalvesBound
import PseudoPrime.Analysis.PrecisePiLogBound
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.Analysis.Meromorphic.Divisor

/-! # Explicit Dirichlet Poisson zero mass at a real parameter -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character satisfying individual GRH and `H ≥ 2`,
the completed-zero Poisson mass at real `H + 1 / 2` is strictly less than
`log (q * H) / 2`. Combine the centered Hadamard identity with signed Gamma and
Euler bounds; the strict saving comes from the explicit lower bound for `log π`.
This is the full-mass input for the inverse-square zero-tail estimate. -/
theorem completed_poissonMass_lt_log {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {H : ℝ} (hH : 2 ≤ H) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (H / Complex.normSq ((((H + 1 / 2 : ℝ) : ℂ)) - ρ))) <
      Real.log ((q : ℝ) * H) / 2 := by
  let σ : ℝ := H + 1 / 2
  let s : ℂ := (σ : ℂ)
  have hs : 1 / 2 < s.re := by
    dsimp only [s, σ]
    simp only [Complex.ofReal_re]
    linarith only [hH]
  have hs1 : (1 : ℝ) ≤ s.re := by
    dsimp only [s, σ]
    simp only [Complex.ofReal_re]
    linarith only [hH]
  have hs0 : 0 < s.re := zero_lt_one.trans_le hs1
  have he :=
    L_logDeriv_sub_gamma_of_regular hne (completed_ne_zero_of_one_le_re hne hs1)
      (gammaFactor_ne_zero_of_re_pos χ hs0)
      (analyticAt_gammaFactor_of_re_pos χ hs0).differentiableAt
  have he' :
    logDeriv χ.completedLFunction s = logDeriv χ.LFunction s + logDeriv χ.gammaFactor s := by
    rw [he]
    ring
  have hm := completed_poissonSum_eq_logDeriv_re hq hRH hp hne hinv hs
  rw [he'] at hm
  have hg := re_gammaLogDeriv_le_log χ hH
  have hl :=
    norm_logDeriv_le_half χ (σ := σ)
      (by
        dsimp only [σ]; linarith only [hH])
      0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at hl
  have hre := Complex.re_le_norm (logDeriv χ.LFunction s)
  have hpi := Analysis.log_pi_ge_2096_div_1831
  have hlog :=
    Real.log_mul (show (q : ℝ) ≠ 0 by exact_mod_cast (NeZero.ne q)) (by linarith only [hH] : H ≠ 0)
  dsimp only [s, σ] at hm hre hl
  simp only [Complex.ofReal_re, add_sub_cancel_right, Complex.add_re] at hm
  rw [hlog]
  linarith only [hm, hg, hl, hre, hpi]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
