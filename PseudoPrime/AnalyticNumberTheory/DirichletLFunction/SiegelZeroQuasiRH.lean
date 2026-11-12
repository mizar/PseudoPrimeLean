/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.SiegelZeroStatement
public import PseudoPrime.AnalyticNumberTheory.GRH.QuasiRiemannHypothesis
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # The uniform real-zero gap under the Dirichlet quasi-Riemann hypothesis -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- The Dirichlet quasi-Riemann hypothesis implies the uniform real-zero
gap statement. Every relevant real zero is at most `7/8`, and the modulus
condition gives `1 ≤ log q`, so the absolute constant `1/8` suffices. -/
theorem siegelZeroUniformBound_of_quasiRH (hQRH : GRH.DirichletQuasiRiemannHypothesis) :
    SiegelZeroUniformBound := by
  refine ⟨(1 / 8 : ℝ), by norm_num only, ?_⟩
  intro q _ hq χ hprim hχ hreal β hβ0 hβ1 hz
  have hβ : β ≤ (7 / 8 : ℝ) := by
    apply le_of_not_gt
    intro ht
    have hs : (7 / 8 : ℝ) < ((β : ℂ)).re := by simpa only [Complex.ofReal_re] using ht
    exact (hQRH q χ (β : ℂ) hs (fun hpole ↦ hχ hpole.1)) hz
  have hqreal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith only [hqreal]
  have hlog : 1 ≤ Real.log (q : ℝ) :=
    (Real.le_log_iff_exp_le hqpos).2 (Real.exp_one_lt_three.le.trans hqreal)
  have hfactor : (1 / 8 : ℝ) ≤ 1 - β := by linarith only [hβ]
  have hlog0 : 0 ≤ Real.log (q : ℝ) := by linarith only [hlog]
  have hm := mul_le_mul_of_nonneg_right hfactor hlog0
  have hn := mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 1 / 8)
  linarith only [hm, hn]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
