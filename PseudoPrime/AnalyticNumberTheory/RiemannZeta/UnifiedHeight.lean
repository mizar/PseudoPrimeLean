/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.HeightSequence
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FarLeftLogDeriv

/-! # Kernel-independent height and rectangle constructions -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/--
The index of a good height chosen beyond the far-left height required at stage `m`.

Taking the natural ceiling makes the existing `RiemannZeta.goodHeightSeq` available while retaining
a height
that dominates the scale used by the far-left estimates.
-/
noncomputable def farLeftGoodHeightIndex (m : ℕ) : ℕ :=
  ⌈farLeftHeightSeq m⌉₊

/-- The common good-height sequence for the four-edge contour limit. -/
noncomputable def unifiedContourHeightSeq (m : ℕ) : ℝ :=
  goodHeightSeq (farLeftGoodHeightIndex m)

/-- The selected good-height indices tend to infinity. -/
theorem tendsto_farLeftGoodHeightIndex_atTop :
    Filter.Tendsto farLeftGoodHeightIndex Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  apply hm.trans
  exact_mod_cast
    (show (m : ℝ) ≤ ⌈farLeftHeightSeq m⌉₊ by
      exact
        (le_trans
          (by
            linarith only [add_one_le_farLeftHeightSeq
                m])
          (Nat.le_ceil (farLeftHeightSeq m))))

/-- The unified contour heights tend to infinity. -/
theorem tendsto_unifiedContourHeightSeq_atTop :
    Filter.Tendsto unifiedContourHeightSeq Filter.atTop Filter.atTop := by
  exact
    tendsto_goodHeightSeq_atTop.comp
      tendsto_farLeftGoodHeightIndex_atTop

/-- The unified height dominates the original far-left height at every stage. -/
theorem farLeftHeightSeq_le_unifiedContourHeightSeq (m : ℕ) :
    farLeftHeightSeq m ≤
      unifiedContourHeightSeq m := by
  calc
    farLeftHeightSeq m ≤
        (farLeftGoodHeightIndex m : ℝ) :=
      Nat.le_ceil (farLeftHeightSeq m)
    _ ≤ 8 + (farLeftGoodHeightIndex m : ℝ) := by linarith only []
    _ ≤ unifiedContourHeightSeq m := by
      exact
        (goodHeightSeq_mem
            (farLeftGoodHeightIndex m)).1

/-- The unified height is at most a fixed additive enlargement of the far-left height. -/
theorem unifiedContourHeightSeq_lt_farLeftHeightSeq_add_ten (m : ℕ) :
    unifiedContourHeightSeq m <
      farLeftHeightSeq m + 10 := by
  have hgood :=
    (goodHeightSeq_mem (farLeftGoodHeightIndex m)).2
  have hceil :
    (farLeftGoodHeightIndex m : ℝ) <
      farLeftHeightSeq m + 1 := by
    exact
      Nat.ceil_lt_add_one (farLeftHeightSeq_pos m).le
  unfold unifiedContourHeightSeq at *
  linarith only [hgood, hceil]

/-- Each unified height retains the zero-avoidance certificate of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.goodHeightSeq`. -/
theorem unifiedContourHeightSeq_good (m : ℕ) :
    ∀ ρ : ℂ,
      riemannZeta ρ = 0 →
        |ρ.im - (8 + (farLeftGoodHeightIndex m : ℝ))| ≤ 2 →
        1 /
            (4 * jensenLogConst *
              Real.log (8 + (farLeftGoodHeightIndex m : ℝ) + 2)) ≤
          |unifiedContourHeightSeq m - ρ.im| := by
  exact goodHeightSeq_good (farLeftGoodHeightIndex m)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
