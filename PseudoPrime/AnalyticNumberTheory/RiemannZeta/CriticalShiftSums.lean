/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.CriticalShiftIntervals

/-! # Sums of shifted critical-line term rectangles -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Membership of a pair in a zipped list implies membership of each component in its source
list. The proof traverses both lists together and does not use indexed access. It connects a
left-endpoint block and a shared shift-phase block to their separate soundness theorems. -/
theorem zip_members {α β : Type} (xs : List α) (ys : List β) (a : α) (b : β)
    (h : (a, b) ∈ xs.zip ys) : a ∈ xs ∧ b ∈ ys := by
  induction xs generalizing ys with
  | nil => simp only [List.zip_nil_left, List.not_mem_nil] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp only [List.zip_nil_right, List.not_mem_nil] at h
    | cons y ys =>
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | h
      · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
      · have hm := ih ys h
        exact ⟨List.mem_cons_of_mem _ hm.1, List.mem_cons_of_mem _ hm.2⟩

/-- Traverse pairs of left-endpoint term witnesses and shared shift-phase witnesses, multiply
their rectangles, and sum the results. The empty list gives the exact zero rectangle; no list
value is retrieved by index. This operation supplies shifted odd-sum certificate blocks. -/
def criticalShiftSum (G e : ℤ) :
    List (CriticalTermWitness × CriticalTermWitness) →
      Analysis.IntegerInterval × Analysis.IntegerInterval
  | [] => (⟨0, 0⟩, ⟨0, 0⟩)
  | p :: ps =>
    dyadicBoxAdd (Analysis.roundedComplexProduct G (p.1.result G e) (p.2.phaseResult G e))
      (criticalShiftSum G e ps)

/-- If each traversed pair's product rectangle contains the designated power term, their
computed sum contains the sum of these terms. Induction combines the head and tail enclosures;
the first witness in each pair supplies the natural base. -/
theorem criticalShiftSum_contains (G e : ℤ) (s : ℂ)
    (data : List (CriticalTermWitness × CriticalTermWitness))
    (h :
      ∀ p ∈ data,
        Analysis.complexIntervalContains
          (Analysis.roundedComplexProduct G (p.1.result G e) (p.2.phaseResult G e)).1
          (Analysis.roundedComplexProduct G (p.1.result G e) (p.2.phaseResult G e)).2 G
          (dyadicPowerTerm s p.1.log.base)) :
    Analysis.complexIntervalContains (criticalShiftSum G e data).1 (criticalShiftSum G e data).2 G
      ((data.map fun p ↦ dyadicPowerTerm s p.1.log.base).sum) := by
  induction data with
  | nil =>
    simp only [criticalShiftSum, List.map_nil, List.sum_nil, Analysis.complexIntervalContains,
      Analysis.IntegerInterval.Contains, Complex.zero_re, Complex.zero_im, Int.cast_zero, zero_div,
      le_refl, and_self]
  | cons p ps ih =>
    have hp := h p List.mem_cons_self
    have hs := ih (fun q hq ↦ h q (List.mem_cons_of_mem _ hq))
    simpa only [criticalShiftSum, List.map_cons, List.sum_cons, dyadicBoxAdd] using
      Analysis.complex_add_contains hp hs

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
