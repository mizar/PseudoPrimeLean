/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.GroupTheory.Exponent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-! # Proper power kernels on prime modular units -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- At a prime p, the E-power kernel is proper if p-1 does not divide E.
A full kernel would annihilate every unit, forcing the cyclic group exponent
p-1 to divide E. This is the local non-Korselt subgroup for MR. -/
theorem local_prime_powerKernel_ne_top_of_not_dvd {p E : ℕ} [Fact p.Prime] (hdiv : ¬p - 1 ∣ E) :
    (powMonoidHom E : (ZMod p)ˣ →* (ZMod p)ˣ).ker ≠ ⊤ := by
  intro htop
  have hall : ∀ u : (ZMod p)ˣ, u ^ E = 1 := by
    intro u
    exact MonoidHom.mem_ker.mp (htop.symm ▸ Subgroup.mem_top u)
  have hexp := Monoid.exponent_dvd_of_forall_pow_eq_one hall
  rw [IsCyclic.exponent_eq_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
    Nat.totient_prime (Fact.out : p.Prime)] at hexp
  exact hdiv hexp

end PseudoPrime.NumberTheory
