/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.IntegratedZeroLedger
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeightCounting
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedGeometry

/-! # Exhaustion of bounded zero ledgers by unified rectangles -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For every nonnegative height `T`, the unified finite contour ledgers
eventually contain all nontrivial zeros of height at most `T`. The contour
height dominates its index, and zeta zeros lie to the left of one. -/
theorem zerosUpTo_eventually_in_unified {T : ℝ} (hT : 0 ≤ T) :
    ∀ᶠ m : ℕ in Filter.atTop,
      zerosUpTo T ⊆
        (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
              (unifiedTauRectangleUpper 2 m)).filter
          (fun ρ ↦ ¬ρ.re < 0) := by
  obtain ⟨N, hN⟩ := exists_nat_ge T
  filter_upwards [Filter.eventually_ge_atTop N] with m hm
  intro ρ hρ
  have hz := (mem_zerosUpTo hT).1 hρ
  have hm' : (N : ℝ) ≤ m := by exact_mod_cast hm
  have hheight : T ≤ unifiedContourHeightSeq m := by
    have h := (add_one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
    linarith only [hN, hm', h]
  have hre := riemannZeta_zero_re_le_one hz.1
  apply Finset.mem_filter.mpr
  constructor
  · apply mem_riemannZetaZerosInAnyRectangle_iff.mpr
    constructor
    · simp only [Rectangle.rectangleClosedBox, Complex.mem_reProdIm, Set.mem_uIcc,
        unifiedRectangleLower, unifiedTauRectangleUpper]
      constructor
      · left
        constructor
        · have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          linarith only [hz.2.1, hm0]
        · linarith only [hre]
      · left
        have hh := abs_le.mp hz.2.2
        constructor <;> linarith only [hh.1, hh.2, hheight]
    · exact hz.1
  · exact not_lt.mpr hz.2.1

/-- At any nonnegative cutoff `A`, the part of a unified contour ledger
through height `A` eventually equals the closed-height zero ledger. This
allows a fixed signed head to be retained when passing to the contour limit. -/
theorem unified_head_eventually_eq {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ m : ℕ in Filter.atTop,
      ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                  (unifiedTauRectangleUpper 2 m)).filter
              (fun ρ ↦ ¬ρ.re < 0)).filter
          (fun ρ ↦ |ρ.im| ≤ A) =
        zerosUpTo A := by
  filter_upwards [zerosUpTo_eventually_in_unified hA] with m hm
  ext ρ
  constructor
  · intro hρ
    have h := Finset.mem_filter.mp hρ
    have hs := Finset.mem_filter.mp h.1
    have hz := (mem_riemannZetaZerosInAnyRectangle_iff.mp hs.1).2
    exact (mem_zerosUpTo hA).2 ⟨hz, not_lt.mp hs.2, h.2⟩
  · intro hρ
    apply Finset.mem_filter.mpr
    exact ⟨hm hρ, ((mem_zerosUpTo hA).1 hρ).2.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
