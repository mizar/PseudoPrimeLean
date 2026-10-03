/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.MillerRabin.Composite

/-! # Discrete witness contracts for Miller–Rabin -/

namespace PseudoPrime.PrimeTest

/-- A residue outside a subgroup containing every canonical pass is a strong-test witness. -/
theorem not_pass_of_outside_subgroup {n : ℕ} {H : Subgroup (ZMod n)ˣ}
    (hpassImage : ∀ x : ZMod n, StrongMillerRabinPass n x → ∃ u ∈ H, (u : ZMod n) = x) {x : ZMod n}
    (houtside : ¬∃ u ∈ H, (u : ZMod n) = x) : ¬StrongMillerRabinPass n x := by
  intro hpass
  exact houtside (hpassImage x hpass)

/-- A bound supplied by any method makes a finite set of tests sufficient for primality.
Completeness of this witness set is an explicit hypothesis; no analytic assumption is implicit. -/
theorem prime_of_bounded_witnesses {n bound : ℕ}
    (hwitness : ¬Nat.Prime n → ∃ a ≤ bound, strongMillerRabinWithBase n a = false)
    (hpass : ∀ a ≤ bound, strongMillerRabinWithBase n a = true) : Nat.Prime n := by
  by_contra h
  obtain ⟨a, ha, hfalse⟩ := hwitness h
  exact Bool.noConfusion ((hpass a ha).symm.trans hfalse)

end PseudoPrime.PrimeTest
