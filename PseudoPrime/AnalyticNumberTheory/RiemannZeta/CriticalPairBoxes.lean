/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalShiftSums

/-! # Direct term enclosures from checked paired boxes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A saved box encloses a direct odd term when the checked saved box equals a paired
witness box and that witness box encloses the term. The list is traversed by membership,
and base two is excluded because the odd-box tree treats it separately. The result is
independent of the concrete tree, endpoint, or certificate table. -/
theorem pair_box_contains (data : List (CriticalTermWitness × CriticalTermWitness))
    (B : ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (C :
      CriticalTermWitness × CriticalTermWitness →
        Analysis.IntegerInterval × Analysis.IntegerInterval)
    (G : ℤ) (s : ℂ) (n : ℕ)
    (hn : n ∈ (data.map (fun p ↦ p.1.log.base)).filter (fun m ↦ decide (m ≠ 2)))
    (hcheck : ∀ p ∈ data, p.1.log.base = 2 ∨ B p.1.log.base = C p)
    (hsound :
      ∀ p ∈ data,
        Analysis.complexIntervalContains (C p).1 (C p).2 G (dyadicPowerTerm s p.1.log.base)) :
    Analysis.complexIntervalContains (B n).1 (B n).2 G (dyadicPowerTerm s n) := by
  have hne : n ≠ 2 := of_decide_eq_true (List.mem_filter.mp hn).2
  obtain ⟨⟨a, b⟩, hab, hbase⟩ := List.mem_map.mp (List.mem_filter.mp hn).1
  change a.log.base = n at hbase
  rcases hcheck (a, b) hab with htwo | heq
  · exact (hne (hbase ▸ htwo)).elim
  · rw [← hbase, heq]
    exact hsound (a, b) hab

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
