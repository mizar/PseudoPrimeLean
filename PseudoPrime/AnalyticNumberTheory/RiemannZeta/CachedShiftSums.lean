/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicShiftBlocks

/-! # Sums of cached term and unit-phase rectangles -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A natural base paired with a fixed-point complex rectangle. Consumers separately prove
whether the rectangle encloses a power term or a unit phase. The literal form permits expensive
phase evaluation to be checked once and reused in multiple later sums. -/
abbrev CachedPowerBox :=
  ℕ × (Analysis.IntegerInterval × Analysis.IntegerInterval)

/-- Traverse pairs of cached term and phase rectangles, multiply them with outward rounding,
and add the products. The first coordinate of each cached entry is its natural base; no list
value is retrieved by index. -/
def cachedShiftSum (G : ℤ) :
    List (CachedPowerBox × CachedPowerBox) → Analysis.IntegerInterval × Analysis.IntegerInterval
  | [] => (⟨0, 0⟩, ⟨0, 0⟩)
  | p :: ps => dyadicBoxAdd (Analysis.roundedComplexProduct G p.1.2 p.2.2) (cachedShiftSum G ps)

/-- If each product of paired cached rectangles encloses the designated complex power, their
computed sum encloses the sum of those powers. Induction traverses the pairs and uses their
first bases, allowing saved phase rectangles to be reused without list indexing. -/
theorem cachedShiftSum_contains (G : ℤ) (s : ℂ) (data : List (CachedPowerBox × CachedPowerBox))
    (h :
      ∀ p ∈ data,
        Analysis.complexIntervalContains (Analysis.roundedComplexProduct G p.1.2 p.2.2).1
          (Analysis.roundedComplexProduct G p.1.2 p.2.2).2 G (dyadicPowerTerm s p.1.1)) :
    Analysis.complexIntervalContains (cachedShiftSum G data).1 (cachedShiftSum G data).2 G
      ((data.map fun p ↦ dyadicPowerTerm s p.1.1).sum) := by
  induction data with
  | nil =>
    simp only [cachedShiftSum, List.map_nil, List.sum_nil, Analysis.complexIntervalContains,
      Analysis.IntegerInterval.Contains, Complex.zero_re, Complex.zero_im, Int.cast_zero, zero_div,
      le_refl, and_self]
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have hs := ih (fun q hq ↦ h q (List.mem_cons_of_mem _ hq))
    simpa only [cachedShiftSum, List.map_cons, List.sum_cons, dyadicBoxAdd] using
      Analysis.complex_add_contains hp hs

/-- A traversed list of certified cached products encloses the odd finite sum when its first
bases form the specified progression. The base equality and list-to-finite-sum conversion
provide the interface needed by the dyadic EM8 recurrence without indexed list access. -/
theorem cachedShiftSum_oddRange (G : ℤ) (s : ℂ) (data : List (CachedPowerBox × CachedPowerBox))
    (a b : ℕ) (hb : data.map (fun p ↦ p.1.1) = (List.range b).map (fun k ↦ 2 * (a + k) + 1))
    (h :
      ∀ p ∈ data,
        Analysis.complexIntervalContains (Analysis.roundedComplexProduct G p.1.2 p.2.2).1
          (Analysis.roundedComplexProduct G p.1.2 p.2.2).2 G (dyadicPowerTerm s p.1.1)) :
    Analysis.complexIntervalContains (cachedShiftSum G data).1 (cachedShiftSum G data).2 G
      (∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1)) := by
  have hsum := cachedShiftSum_contains G s data h
  have hid :
    (data.map fun p ↦ dyadicPowerTerm s p.1.1).sum =
      ∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1) := by
    have hmap := congrArg (List.map (dyadicPowerTerm s)) hb
    simp only [List.map_map, Function.comp_def] at hmap
    rw [hmap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rw [hid] at hsum
  exact hsum

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
