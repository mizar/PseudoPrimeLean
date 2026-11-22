/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.DyadicEM8Blocks
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalShiftSums

/-! # Shifted odd-block enclosures -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The computed rectangle sum over concatenated pairs is the coordinatewise sum of the
two computed rectangles. This permits cached shifted partial sums to be reused in larger blocks
without recalculating individual rotations. -/
theorem criticalShiftSum_append (G e : ℤ)
    (xs ys : List (CriticalTermWitness × CriticalTermWitness)) :
    criticalShiftSum G e (xs ++ ys) =
      dyadicBoxAdd (criticalShiftSum G e xs) (criticalShiftSum G e ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, criticalShiftSum, dyadicBoxAdd, Analysis.IntegerInterval.add,
      Int.zero_add]
  | cons w ws ih =>
    simp only [List.cons_append, criticalShiftSum, ih, dyadicBoxAdd, Analysis.IntegerInterval.add,
      Int.add_assoc]

/-- A list of certified shifted terms encloses an odd finite sum when the first components'
bases form the specified progression. The proof converts the traversed list sum to a finite
sum; no witness is selected by a list index. -/
theorem criticalShiftSum_oddRange (G e : ℤ) (s : ℂ)
    (data : List (CriticalTermWitness × CriticalTermWitness)) (a b : ℕ)
    (hb : data.map (fun p ↦ p.1.log.base) = (List.range b).map (fun k ↦ 2 * (a + k) + 1))
    (h :
      ∀ p ∈ data,
        Analysis.complexIntervalContains
          (Analysis.roundedComplexProduct G (p.1.result G e) (p.2.phaseResult G e)).1
          (Analysis.roundedComplexProduct G (p.1.result G e) (p.2.phaseResult G e)).2 G
          (dyadicPowerTerm s p.1.log.base)) :
    Analysis.complexIntervalContains (criticalShiftSum G e data).1 (criticalShiftSum G e data).2 G
      (∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1)) := by
  have hsum := criticalShiftSum_contains G e s data h
  have hid :
    (data.map fun p ↦ dyadicPowerTerm s p.1.log.base).sum =
      ∑ k ∈ Finset.range b, dyadicPowerTerm s (2 * (a + k) + 1) := by
    have hmap := congrArg (List.map (dyadicPowerTerm s)) hb
    simp only [List.map_map, Function.comp_def] at hmap
    rw [hmap, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range]
  rw [hid] at hsum
  exact hsum

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
