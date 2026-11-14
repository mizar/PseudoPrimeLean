/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlockBound

/-! # First log-height interval of the phase certificate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For ordinates satisfying the low-zero bracket conditions, the signed
head is at most 51/100 on the log-height interval [13.81, 13.814]. The
first rotation block contains this interval and supplies the bound. -/
theorem phase1381_first_interval (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (6907 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  exact phaseFirstBlock_bound g hl hu ⟨hv.1, by linarith only [hv.2]⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
