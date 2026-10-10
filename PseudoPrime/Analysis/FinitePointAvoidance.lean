/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

/-!
# Avoiding finitely many points in a real interval

A volume comparison selects a point separated from each forbidden point.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If positive-radius intervals around a finite set have total length less
than L>0, some point of [a,a+L] has distance at least c from every forbidden
point. Compare the interval volume with the sum of excluded interval volumes.
This selects zero-avoiding heights without any assumption about an L function. -/
theorem exists_avoiding_point_length {S : Finset ℝ} {c a L : ℝ} (hc : 0 < c) (_hL : 0 < L)
    (hlen : 2 * c * S.card < L) : ∃ T ∈ Set.Icc a (a + L), ∀ y ∈ S, c ≤ |T - y| := by
  by_contra hcon
  push Not at hcon
  have hsub : Set.Icc a (a + L) ⊆ ⋃ y ∈ S, Set.Ioo (y - c) (y + c) := by
    intro T hT
    obtain ⟨y, hyS, hy⟩ := hcon T hT
    simp only [Set.mem_iUnion]
    rw [abs_lt] at hy
    exact ⟨y, hyS, by constructor <;> linarith only [hy.1, hy.2]⟩
  have hsum_eq :
    ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) * S.card := by
    have hterm : ∀ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) = ENNReal.ofReal (2 * c) :=
      fun y _ ↦ by
      rw [Real.volume_Ioo]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hfinal : ENNReal.ofReal L ≤ ENNReal.ofReal (2 * c) * (S.card : ENNReal) := by
    calc
      ENNReal.ofReal L = MeasureTheory.volume (Set.Icc a (a + L)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
      _ ≤ MeasureTheory.volume (⋃ y ∈ S, Set.Ioo (y - c) (y + c)) := MeasureTheory.measure_mono hsub
      _ ≤ ∑ y ∈ S, MeasureTheory.volume (Set.Ioo (y - c) (y + c)) :=
        MeasureTheory.measure_biUnion_finset_le S _
      _ = ENNReal.ofReal (2 * c) * S.card := hsum_eq
  rw [← ENNReal.ofReal_natCast S.card, ←
    ENNReal.ofReal_mul (le_of_lt (mul_pos (by norm_num only) hc)),
    ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (le_of_lt (mul_pos (by norm_num only) hc)) (Nat.cast_nonneg _))] at hfinal
  linarith only [hfinal, hlen]

/-- A finite set whose excluded intervals have total length less than one
leaves a point of [a,a+1] at distance at least c from every forbidden point.
Apply the arbitrary-length interval result with L=1. This unit-window form
is used to choose heights for explicit-formula contours. -/
theorem exists_avoiding_point {S : Finset ℝ} {c a : ℝ} (hc : 0 < c) (hlen : 2 * c * S.card < 1) :
    ∃ T ∈ Set.Icc a (a + 1), ∀ y ∈ S, c ≤ |T - y| := by
  exact exists_avoiding_point_length hc zero_lt_one hlen

end PseudoPrime.Analysis
