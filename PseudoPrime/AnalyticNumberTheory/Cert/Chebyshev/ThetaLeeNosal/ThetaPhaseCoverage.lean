/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPhaseGrid
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! # Real interval covered by the generated phase cells -/

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

/-- A bound proved on each generated closed cell holds throughout the logarithmic middle band.
Induction over adjacent cells includes both outer endpoints. -/
public theorem phaseGrid_cover {P : ℝ → Prop}
    (hc :
      ∀ i : Fin 320,
        ∀ x : ℝ, phaseTick i.castSucc / (512 : ℝ) ≤ x → x ≤ phaseTick i.succ / (512 : ℝ) → P x)
    {x : ℝ} (hl : 35 / 2 ≤ x) (hr : x ≤ 53 / 2) : P x := by
  have h : ∀ i : Fin 320, x ≤ phaseTick i.succ / (512 : ℝ) → P x := by
    refine Fin.induction ?_ ?_
    · intro hx
      apply hc 0 x _ hx
      change (phaseTick 0 : ℝ) / 512 ≤ x
      rw [phaseTick_first]
      linarith only [hl]
    · intro i ih hx
      rcases le_total x (phaseTick i.castSucc.succ / (512 : ℝ)) with hprev | hnext
      · exact ih hprev
      · exact hc i.succ x hnext hx
  apply h (Fin.last 319)
  change x ≤ (phaseTick (Fin.last 320) : ℝ) / 512
  rw [phaseTick_last]
  linarith only [hr]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
