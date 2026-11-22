/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalTermWitness

/-! # Traversal-based sums of critical-line term certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Add the computed rectangles of a list of critical-term witnesses at a common scale. The
empty sum is the exact zero rectangle. The recursion consumes the head and tail directly,
without indexing the list, and supplies partial sums for endpoint certificates. -/
def criticalTermSum (G e : ℤ) :
    List CriticalTermWitness → Analysis.IntegerInterval × Analysis.IntegerInterval
  | [] => (⟨0, 0⟩, ⟨0, 0⟩)
  | w :: ws => dyadicBoxAdd (w.result G e) (criticalTermSum G e ws)

/-- If every witness rectangle in a finite list contains its corresponding complex power, the
computed rectangle contains the sum of those powers. Induction adds the head enclosure to the
tail enclosure; the empty list contributes zero. This soundness theorem permits a certificate
to assemble block sums without retrieving list values by index. -/
theorem criticalTermSum_contains (G e : ℤ) (s : ℂ) (data : List CriticalTermWitness)
    (h :
      ∀ w ∈ data,
        Analysis.complexIntervalContains (w.result G e).1 (w.result G e).2 G
          (dyadicPowerTerm s w.log.base)) :
    Analysis.complexIntervalContains (criticalTermSum G e data).1 (criticalTermSum G e data).2 G
      ((data.map fun w ↦ dyadicPowerTerm s w.log.base).sum) := by
  induction data with
  | nil =>
    simp only [criticalTermSum, List.map_nil, List.sum_nil, Analysis.complexIntervalContains,
      Analysis.IntegerInterval.Contains, Complex.zero_re, Complex.zero_im, Int.cast_zero, zero_div,
      le_refl, and_self]
  | cons w ws ih =>
    have hw := h w (List.mem_cons_self)
    have hs := ih (fun u hu ↦ h u (List.mem_cons_of_mem _ hu))
    simpa only [criticalTermSum, List.map_cons, List.sum_cons, dyadicBoxAdd] using
      Analysis.complex_add_contains hw hs

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
