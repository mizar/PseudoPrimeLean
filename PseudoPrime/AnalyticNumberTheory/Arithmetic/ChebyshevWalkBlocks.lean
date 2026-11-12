/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkBlockSound

/-! # Sequential crossing certificates for the Chebyshev psi function -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A block contains sequential walk entries, its candidate end state, and
integer lower estimates for the square-root envelopes at its endpoints. -/
structure PsiWalkBlock where
  entries : List PsiWalkEntry
  dest : PsiWalkState
  ca : ℕ
  cb : ℕ

/-- Check both the sequential walk and the crossing inequalities for a block. -/
def psiWalkBlockCheck (S : ℕ) (s : PsiWalkState) (b : PsiWalkBlock) : Bool :=
  decide (psiWalk S s b.entries = some b.dest) && psiWalkBlockGuard S s b.dest b.ca b.cb

/-- Check a list of blocks in order, passing each final state to its successor. -/
def psiWalkBlocksCheck (S : ℕ) : PsiWalkState → List PsiWalkBlock → Bool
  | _, [] => true
  | s, b :: bs => psiWalkBlockCheck S s b && psiWalkBlocksCheck S b.dest bs

/-- Return the final state of a sequential block list, or the start if empty. -/
def psiWalkBlocksEnd : PsiWalkState → List PsiWalkBlock → PsiWalkState
  | s, [] => s
  | _, b :: bs => psiWalkBlocksEnd b.dest bs

/-- A checked sequence of blocks preserves the walk invariant and proves the
four-fifths square-root psi estimate from the initial index to the final index.
Each power entry must separately carry a certified logarithm enclosure. -/
theorem psi_walk_blocks_sound {S : ℕ} {s : PsiWalkState} {bs : List PsiWalkBlock}
    (hs : PsiWalkValid S s) (hv : bs.Forall fun b => b.entries.Forall (PsiWalkEntryValid S))
    (hc : psiWalkBlocksCheck S s bs = true) :
    PsiWalkValid S (psiWalkBlocksEnd s bs) ∧
      ∀ x : ℝ,
        (s.n : ℝ) ≤ x →
          x < (psiWalkBlocksEnd s bs).n → |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  induction bs generalizing s with
  | nil =>
    constructor
    · exact hs
    · intro x ha hb
      simp only [psiWalkBlocksEnd] at hb
      exact False.elim ((not_lt_of_ge ha) hb)
  | cons b bs ih =>
    simp only [List.forall_cons] at hv
    have hc' := Bool.and_eq_true_iff.mp hc
    have hp := Bool.and_eq_true_iff.mp hc'.1
    have hw : psiWalk S s b.entries = some b.dest := of_decide_eq_true hp.1
    have ht := psi_walk_sound hs hv.1 hw
    have hr := ih ht hv.2 hc'.2
    constructor
    · exact hr.1
    · intro x ha hb
      by_cases h : x < (b.dest.n + 1 : ℕ)
      · exact psi_walk_block_guard_sound hs ht hp.2 ha h
      · apply hr.2 x
        · have h' : (b.dest.n : ℝ) + 1 ≤ x := by
            simpa only [Nat.cast_add, Nat.cast_one] using le_of_not_gt h
          linarith only [h']
        · exact hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
