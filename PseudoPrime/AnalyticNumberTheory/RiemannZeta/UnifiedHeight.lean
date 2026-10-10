/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HeightSequence
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FarLeftLogDeriv

/-! # Kernel-independent height and rectangle constructions -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/--
The index of a good height chosen beyond the far-left height required at stage `m`.

Taking the natural ceiling makes the existing `RiemannZeta.goodHeightSeq` available while retaining
a height
that dominates the scale used by the far-left estimates.
-/
noncomputable def farLeftGoodHeightIndex (m : ℕ) : ℕ :=
  ⌈farLeftHeightSeq m⌉₊

/-- At natural stage `m`, select the good zeta-avoiding height at index
`ceil (farLeftHeightSeq m)`. It dominates the far-left height while remaining less than
that height plus ten. This common sequence supports both horizontal-edge decay and
far-left estimates in the four-edge contour limit. -/
noncomputable def unifiedContourHeightSeq (m : ℕ) : ℝ :=
  goodHeightSeq (farLeftGoodHeightIndex m)

/-- The indices `ceil (farLeftHeightSeq m)` tend to infinity with natural `m`.
The far-left sequence dominates `m + 1`, and its natural ceiling dominates its value,
so the selected index is at least `m`. This permits composition with the good-height limit. -/
theorem tendsto_farLeftGoodHeightIndex_atTop :
    Filter.Tendsto farLeftGoodHeightIndex Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  apply hm.trans
  exact_mod_cast
    (show (m : ℝ) ≤ ⌈farLeftHeightSeq m⌉₊ by
      exact
        (le_trans (by linarith only [add_one_le_farLeftHeightSeq m])
          (Nat.le_ceil (farLeftHeightSeq m))))

/-- The unified contour height tends to infinity with the stage index.
Compose divergence of the good-height sequence with divergence of its selected indices.
This supplies the growing-height hypothesis for contour limits on the common rectangles. -/
theorem tendsto_unifiedContourHeightSeq_atTop :
    Filter.Tendsto unifiedContourHeightSeq Filter.atTop Filter.atTop := by
  exact tendsto_goodHeightSeq_atTop.comp tendsto_farLeftGoodHeightIndex_atTop

/-- At every natural stage `m`, `farLeftHeightSeq m ≤ unifiedContourHeightSeq m`.
The ceiling dominates the original height, and the good height is at least its index plus
eight. This transports the far-left estimates to the unified contour. -/
theorem farLeftHeightSeq_le_unifiedContourHeightSeq (m : ℕ) :
    farLeftHeightSeq m ≤ unifiedContourHeightSeq m := by
  calc
    farLeftHeightSeq m ≤ (farLeftGoodHeightIndex m : ℝ) := Nat.le_ceil (farLeftHeightSeq m)
    _ ≤ 8 + (farLeftGoodHeightIndex m : ℝ) := by linarith only []
    _ ≤ unifiedContourHeightSeq m := by exact (goodHeightSeq_mem (farLeftGoodHeightIndex m)).1

/-- At every natural stage `m`, the unified height is strictly less than
`farLeftHeightSeq m + 10`. Its good-height interval gives the upper bound index plus nine,
and the ceiling is less than the original height plus one.
This controls the enlargement when reusing far-left decay estimates. -/
theorem unifiedContourHeightSeq_lt_farLeftHeightSeq_add_ten (m : ℕ) :
    unifiedContourHeightSeq m < farLeftHeightSeq m + 10 := by
  have hgood := (goodHeightSeq_mem (farLeftGoodHeightIndex m)).2
  have hceil : (farLeftGoodHeightIndex m : ℝ) < farLeftHeightSeq m + 1 := by
    exact Nat.ceil_lt_add_one (farLeftHeightSeq_pos m).le
  unfold unifiedContourHeightSeq at *
  linarith only [hgood, hceil]

/-- Each unified height retains the zero-avoidance certificate of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.goodHeightSeq`. -/
theorem unifiedContourHeightSeq_good (m : ℕ) :
    ∀ ρ : ℂ,
      riemannZeta ρ = 0 →
        |ρ.im - (8 + (farLeftGoodHeightIndex m : ℝ))| ≤ 2 →
        1 / (4 * jensenLogConst * Real.log (8 + (farLeftGoodHeightIndex m : ℝ) + 2)) ≤
          |unifiedContourHeightSeq m - ρ.im| := by
  exact goodHeightSeq_good (farLeftGoodHeightIndex m)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
