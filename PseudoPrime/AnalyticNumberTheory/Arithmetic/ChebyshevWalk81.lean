/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkBlocks
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt81Checker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtGeneral

/-! # Coefficient-81/100 crossing checks for shared psi walks -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Check the scaled endpoint crossing inequalities for the `81 / 100` envelope.
The log and psi values in the walk states are validated separately. -/
def psi81WalkGuard (S : ℕ) (s t : PsiWalkState) (ca cb : ℕ) : Bool :=
  decide
    (0 < S ∧
      ca ^ 2 ≤ 656100 * s.n ∧
      cb ^ 2 ≤ 656100 * (t.n + 1) ∧
      1000 * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb ∧ 1000 * t.psiHi ≤ 1000 * S * s.n + S * ca)

/-- Valid walk endpoints and an `81 / 100` crossing guard give the error bound on the entire
half-open interval. The proof reuses the general square-root endpoint theorem. -/
theorem psi81_walk_guard_sound {S : ℕ} {s t : PsiWalkState} {ca cb : ℕ} {x : ℝ}
    (hs : PsiWalkValid S s) (ht : PsiWalkValid S t) (hg : psi81WalkGuard S s t ca cb = true)
    (hax : (s.n : ℝ) ≤ x) (hxb : x < (t.n + 1 : ℕ)) :
    |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
  have hc :
    0 < S ∧
      ca ^ 2 ≤ 656100 * s.n ∧
      cb ^ 2 ≤ 656100 * (t.n + 1) ∧
      1000 * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb ∧ 1000 * t.psiHi ≤ 1000 * S * s.n + S * ca :=
    of_decide_eq_true hg
  have hS0 : (0 : ℝ) < S := Nat.cast_pos.mpr hc.1
  have hleft : (s.psiLo : ℝ) / S ≤ Chebyshev.psi s.n := by
    apply (div_le_iff₀ hS0).2
    simpa only [mul_comm] using hs.2.2.2.1
  have hright : Chebyshev.psi t.n ≤ (t.psiHi : ℝ) / S := by
    apply (le_div_iff₀ hS0).2
    simpa only [mul_comm] using ht.2.2.2.2
  have hta : (1 : ℝ) ≤ s.n := by exact_mod_cast hs.1
  have ht' : Chebyshev.psi ((t.n + 1) - 1 : ℕ) ≤ (t.psiHi : ℝ) / S := by
    simpa only [Nat.add_sub_cancel] using hright
  have hl' : (1000 : ℝ) * S * (t.n + 1) ≤ 1000 * s.psiLo + S * cb := by exact_mod_cast hc.2.2.2.1
  have hu' : (1000 : ℝ) * t.psiHi ≤ 1000 * S * s.n + S * ca := by exact_mod_cast hc.2.2.2.2
  have hl : ((t.n + 1 : ℕ) : ℝ) ≤ (s.psiLo : ℝ) / S + (cb : ℝ) / 1000 := by
    have h : ((t.n + 1 : ℕ) : ℝ) - (cb : ℝ) / 1000 ≤ (s.psiLo : ℝ) / S := by
      apply (le_div_iff₀ hS0).2
      norm_num only [Nat.cast_add, Nat.cast_one]
      nlinarith only [hl']
    linarith only [h]
  have hu : (t.psiHi : ℝ) / S ≤ (s.n : ℝ) + (ca : ℝ) / 1000 := by
    apply (div_le_iff₀ hS0).2
    nlinarith only [hu']
  exact
    psi_sqrt_cross_cell (c := (81 / 100 : ℝ)) (by norm_num only) (by norm_num only) hta hax hxb
      hleft ht' (psi81_scaled_sqrt_lower hc.2.1) (psi81_scaled_sqrt_lower hc.2.2.1) hl hu

/-- Check a walk block together with its `81 / 100` crossing guard. -/
def psi81WalkBlockCheck (S : ℕ) (s : PsiWalkState) (b : PsiWalkBlock) : Bool :=
  decide (psiWalk S s b.entries = some b.dest) && psi81WalkGuard S s b.dest b.ca b.cb

/-- Check adjacent walk blocks by consuming the block list sequentially. -/
def psi81WalkBlocksCheck (S : ℕ) : PsiWalkState → List PsiWalkBlock → Bool
  | _, [] => true
  | s, b :: bs => psi81WalkBlockCheck S s b && psi81WalkBlocksCheck S b.dest bs

/-- A checked walk preserves its state invariant and proves the `81 / 100` bound throughout its
range. Prime-power logarithm enclosures are independent inputs to this table-free theorem. -/
theorem psi81_walk_blocks_sound {S : ℕ} {s : PsiWalkState} {bs : List PsiWalkBlock}
    (hs : PsiWalkValid S s) (hv : bs.Forall fun b => b.entries.Forall (PsiWalkEntryValid S))
    (hc : psi81WalkBlocksCheck S s bs = true) :
    PsiWalkValid S (psiWalkBlocksEnd s bs) ∧
      ∀ x : ℝ,
        (s.n : ℝ) ≤ x →
          x < (psiWalkBlocksEnd s bs).n → |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x := by
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
      · exact psi81_walk_guard_sound hs ht hp.2 ha h
      · apply hr.2 x
        · have h' : (b.dest.n : ℝ) + 1 ≤ x := by
            simpa only [Nat.cast_add, Nat.cast_one] using le_of_not_gt h
          linarith only [h']
        · exact hb

/-- A table-free segment transforms a valid initial state into a valid final state and proves
the `81 / 100` psi bound between their indices. Independently certified segments can be composed. -/
def Psi81SqrtSegment (S : ℕ) (s t : PsiWalkState) : Prop :=
  PsiWalkValid S s →
    PsiWalkValid S t ∧
      ∀ x : ℝ, (s.n : ℝ) ≤ x → x < t.n → |Chebyshev.psi x - x| ≤ (81 / 100 : ℝ) * Real.sqrt x

/-- Two adjacent table-free segments compose, allowing balanced aggregation of independent
certificates without exposing their calculation entries. -/
theorem psi81_segment_comp {S : ℕ} {a b c : PsiWalkState} (hab : Psi81SqrtSegment S a b)
    (hbc : Psi81SqrtSegment S b c) : Psi81SqrtSegment S a c := by
  intro ha
  have hb := hab ha
  have hc := hbc hb.1
  refine ⟨hc.1, ?_⟩
  intro x hax hxc
  by_cases hxb : x < (b.n : ℝ)
  · exact hb.2 x hax hxb
  · exact hc.2 x (le_of_not_gt hxb) hxc

/-- Independently checked walk entries and guards provide the corresponding table-free segment. -/
theorem psi81_walk_segment {S : ℕ} {s : PsiWalkState} {bs : List PsiWalkBlock}
    (hv : bs.Forall fun b => b.entries.Forall (PsiWalkEntryValid S))
    (hc : psi81WalkBlocksCheck S s bs = true) : Psi81SqrtSegment S s (psiWalkBlocksEnd s bs) := by
  intro hs
  exact psi81_walk_blocks_sound hs hv hc

end PseudoPrime.AnalyticNumberTheory.Arithmetic
