/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable

/-! # Lower-bound rows for weighted prime-product counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A row bounded by the unbounded-knapsack update is a lower bound for the
new weighted count when the preceding row bounds the previous count. Strong
induction on the budget handles the in-row recurrence. -/
theorem weightedPrimeCount_row_lower (p : ℕ) (ps : List ℕ) (old new : ℕ → ℕ) (N : ℕ) (hp : 0 < p)
    (hold : ∀ h ≤ N, old h ≤ weightedPrimeCount id ps h)
    (hrow : ∀ h ≤ N, new h ≤ if p ≤ h then old h + new (h - p) else old h) :
    ∀ h ≤ N, new h ≤ weightedPrimeCount id (p :: ps) h := by
  intro h
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro hN
    have hstep := hrow h hN
    conv_rhs => rw [weightedPrimeCount.eq_def]
    dsimp only [id_eq]
    rw [dite_eq_left hp]
    by_cases hfit : p ≤ h
    · simp only [hfit, ite_true, dite_true] at hstep ⊢
      exact
        hstep.trans
          (Nat.add_le_add (hold h hN)
            (ih (h - p) (Nat.sub_lt (lt_of_lt_of_le hp hfit) hp) ((Nat.sub_le _ _).trans hN)))
    · simp only [hfit, ite_false, dite_false] at hstep ⊢
      exact hstep.trans (hold h hN)

/-- A checked row preserves lower bounds for the weighted count, even when
the preceding row is only a lower bound rather than the exact count. -/
theorem weightedPrimeRow_lower (p N : ℕ) (ps : List ℕ) (old new : Array ℕ)
    (hc : weightedPrimeRowCheck p N old new = true)
    (hold : ∀ h ≤ N, old.getD h 0 ≤ weightedPrimeCount id ps h) :
    ∀ h ≤ N, new.getD h 0 ≤ weightedPrimeCount id (p :: ps) h := by
  apply
    weightedPrimeCount_row_lower p ps (fun h ↦ old.getD h 0) (fun h ↦ new.getD h 0) N
      (weightedPrimeRowCheck_sound p N old new hc).1 hold
  intro h hh
  exact le_of_eq ((weightedPrimeRowCheck_sound p N old new hc).2 h hh)

end PseudoPrime.PrimeTestBounds.MillerRabin
