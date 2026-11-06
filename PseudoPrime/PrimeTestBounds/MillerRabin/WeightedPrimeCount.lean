/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeFamily

/-! # Recurrence for weighted repeated-factor counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Count multisets supported on a list of labels under an integer weight
budget by the unbounded-knapsack recurrence. A zero weight returns zero;
the correctness theorem applies to positive weights and duplicate-free lists. -/
def weightedPrimeCount (w : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 1
  | p :: ps, H =>
    if _hpos : 0 < w p then
      if _hfit : w p ≤ H then weightedPrimeCount w ps H + weightedPrimeCount w (p :: ps) (H - w p)
      else weightedPrimeCount w ps H
    else 0
termination_by xs H => (H, xs.length)
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | exact Prod.Lex.right _ (Nat.lt_succ_self _)
    | exact Prod.Lex.left _ _ (Nat.sub_lt (lt_of_lt_of_le _hpos _hfit) _hpos)

/-- For a duplicate-free list with positive weights, the recurrence counts
exactly the finite family of supported multisets whose total weight is at most
the budget. Strong induction on the budget and list induction match the two
branches to the previously proved family cardinality identities. -/
theorem weightedPrimeCount_eq_card (w : ℕ → ℕ) (H : ℕ) (xs : List ℕ) (hn : xs.Nodup)
    (hw : ∀ p ∈ xs, 0 < w p) :
    weightedPrimeCount w xs H = (weightedPrimeFamily xs.toFinset w H).card := by
  induction H using Nat.strong_induction_on generalizing xs with
  | h H ih =>
    induction xs with
    | nil =>
      rw [weightedPrimeCount.eq_def, List.toFinset_nil, weightedPrimeFamily_empty,
        Finset.card_singleton]
    | cons p ps il =>
      have hnp := (List.nodup_cons.mp hn).1
      have hnps := (List.nodup_cons.mp hn).2
      have hpos : 0 < w p := hw p (List.mem_cons_self)
      have hwps : ∀ q ∈ ps, 0 < w q := fun q hq ↦ hw q (List.mem_cons_of_mem p hq)
      have hwset : ∀ q ∈ (p :: ps).toFinset, 1 ≤ w q := fun q hq ↦ hw q (List.mem_toFinset.mp hq)
      have hp : p ∈ (p :: ps).toFinset := List.mem_toFinset.mpr (List.mem_cons_self)
      have herase : ((p :: ps).toFinset).erase p = ps.toFinset := by
        rw [List.toFinset_cons, Finset.erase_insert (fun h ↦ hnp (List.mem_toFinset.mp h))]
      rw [weightedPrimeCount.eq_def]
      dsimp only
      rw [dite_eq_left hpos]
      by_cases hfit : w p ≤ H
      · rw [dite_eq_left hfit, il hnps hwps,
          ih (H - w p) (Nat.sub_lt (lt_of_lt_of_le hpos hfit) hpos) (p :: ps) hn hw,
          weightedPrimeFamily_card_step _ _ H p hp hwset hfit, herase]
      · rw [dite_eq_right hfit, il hnps hwps,
          weightedPrimeFamily_remove_heavy _ _ H p hwset (Nat.lt_of_not_ge hfit), herase]

/-- The recurrence depends on labels only through their weights. Mapping a
label list to its weight list and using the identity weight function preserves
the count, including when different labels have the same weight. This lets
the prime-supply construction share one numerical certificate per weight list. -/
theorem weightedPrimeCount_map_weights (w : ℕ → ℕ) (H : ℕ) (xs : List ℕ) :
    weightedPrimeCount w xs H = weightedPrimeCount id (xs.map w) H := by
  induction H using Nat.strong_induction_on generalizing xs with
  | h H ih =>
    induction xs with
    | nil => rw [List.map_nil, weightedPrimeCount.eq_def, weightedPrimeCount.eq_def]
    | cons p ps
      il =>
      rw [List.map_cons, weightedPrimeCount.eq_def, weightedPrimeCount.eq_def]
      dsimp only [id_eq]
      by_cases hp : 0 < w p
      · simp only [hp, dite_true]
        by_cases hf : w p ≤ H
        · simp only [hf, dite_true, il,
            ih (H - w p) (Nat.sub_lt (lt_of_lt_of_le hp hf) hp) (p :: ps), List.map_cons]
        · simp only [hf, dite_false, il]
      · simp only [hp, dite_false]

/-- If a duplicate-free label list has the prescribed positive weight list,
the recurrence evaluated on the weights is exactly the cardinality of the
weighted multiset family on those labels. Distinct labels may share a weight. -/
theorem weightedPrimeCount_weights_eq_card (w : ℕ → ℕ) (H : ℕ) (xs weights : List ℕ) (hn : xs.Nodup)
    (hw : ∀ p ∈ xs, 0 < w p) (he : xs.map w = weights) :
    weightedPrimeCount id weights H = (weightedPrimeFamily xs.toFinset w H).card :=
  (congrArg (fun ys ↦ weightedPrimeCount id ys H) he).symm.trans
    ((weightedPrimeCount_map_weights w H xs).symm.trans (weightedPrimeCount_eq_card w H xs hn hw))

/-- A row satisfying the unbounded-knapsack update through budget `N`
contains the recurrence counts after adding a positive weight, provided the
preceding row is correct. Strong induction justifies the in-row dependency on
the reduced budget. This is the soundness step for finite DP certificates. -/
theorem weightedPrimeCount_row_sound (p : ℕ) (ps : List ℕ) (old new : ℕ → ℕ) (N : ℕ) (hp : 0 < p)
    (hold : ∀ h ≤ N, old h = weightedPrimeCount id ps h)
    (hrow : ∀ h ≤ N, new h = if p ≤ h then old h + new (h - p) else old h) :
    ∀ h ≤ N, new h = weightedPrimeCount id (p :: ps) h := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hN
    rw [hrow h hN, weightedPrimeCount.eq_def]
    dsimp only [id_eq]
    rw [dite_eq_left hp]
    by_cases hfit : p ≤ h
    · simp only [hfit, ite_true, dite_true, hold h hN,
        ih (h - p) (Nat.sub_lt (lt_of_lt_of_le hp hfit) hp) ((Nat.sub_le _ _).trans hN)]
    · simp only [hfit, ite_false, dite_false, hold h hN]

end PseudoPrime.PrimeTestBounds.MillerRabin
