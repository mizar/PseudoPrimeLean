/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic

/-! Elementary bounds for odd composite numbers. -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- An odd composite natural number above one is at least nine. The finitely many smaller
odd numbers above one are prime, as checked by the kernel. This supplies an elementary
lower bound for arguments about odd composite moduli. -/
theorem nine_le_odd_composite {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime) : 9 ≤ n := by
  by_contra h9
  have hp : ∀ k : Fin 9, 1 < k.val → Odd k.val → k.val.Prime := by decide +kernel
  exact hc (hp ⟨n, Nat.lt_of_not_ge h9⟩ hn ho)

end PseudoPrime.NumberTheory
