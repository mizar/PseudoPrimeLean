/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Composite

/-! # Discrete witness contracts for Miller–Rabin -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
A residue `x` outside the image of the unit subgroup `H` fails the canonical Strong pass.
The premise `hpassImage` puts every passing residue in that image, while `houtside` excludes
`x` from it. Applying these two hypotheses proves the negation directly.
This discrete bridge converts subgroup exclusion results into Miller–Rabin witnesses.
-/
theorem not_pass_of_outside_subgroup {n : ℕ} {H : Subgroup (ZMod n)ˣ}
    (hpassImage : ∀ x : ZMod n, StrongMillerRabinPass n x → ∃ u ∈ H, (u : ZMod n) = x) {x : ZMod n}
    (houtside : ¬∃ u ∈ H, (u : ZMod n) = x) : ¬StrongMillerRabinPass n x := by
  intro hpass
  exact houtside (hpassImage x hpass)

/--
A complete finite base range can certify primality of `n`.
`hwitness` must supply a failing base `a ≤ bound` for every non-prime input, and `hpass` states
that all bases in that range pass. Under an assumed non-primality, the supplied witness
contradicts the distinct Boolean results. Analytic witness-bound theorems may discharge
`hwitness`, but no GRH or range-completeness assumption is implicit in this theorem.
-/
theorem prime_of_bounded_witnesses {n bound : ℕ}
    (hwitness : ¬Nat.Prime n → ∃ a ≤ bound, strongMillerRabinWithBase n a = false)
    (hpass : ∀ a ≤ bound, strongMillerRabinWithBase n a = true) : Nat.Prime n := by
  by_contra h
  obtain ⟨a, ha, hfalse⟩ := hwitness h
  exact Bool.noConfusion ((hpass a ha).symm.trans hfalse)

end PseudoPrime.PrimeTest
