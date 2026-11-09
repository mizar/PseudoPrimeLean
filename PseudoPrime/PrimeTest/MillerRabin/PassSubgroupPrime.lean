/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Prime
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import Mathlib.GroupTheory.Index

/-! Prime moduli and subgroups containing Miller–Rabin passes. -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Every unit modulo a prime passes the strong Miller–Rabin test.
Represent the unit by its natural residue, use its coprimality with the prime modulus,
and transfer the executable prime-pass theorem to the canonical residue predicate.
This connects prime correctness to subgroup arguments. -/
theorem strongPass_of_prime_unit {n : ℕ} [NeZero n] (hp : n.Prime) (u : (ZMod n)ˣ) :
    StrongMillerRabinPass n (u : ZMod n) := by
  have hu : IsUnit (((u : ZMod n).val : ℕ) : ZMod n) := by
    rw [ZMod.natCast_zmod_val]
    exact u.isUnit
  have hc := (ZMod.isUnit_iff_coprime (u : ZMod n).val n).mp hu
  have hs :=
    strongMillerRabinWithBase_eq_true_iff_pass.mp (strongMillerRabinWithBase_of_prime hp hc)
  simpa only [ZMod.natCast_zmod_val] using hs

/-- A subgroup of index greater than one that contains every strong-test pass
cannot occur at a prime modulus. For a prime, every unit passes, so pass containment
would make the subgroup the whole unit group and its index one. This lets witness
arguments derive compositeness from their subgroup hypothesis. -/
theorem not_prime_of_passSubgroup_index {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    (hi : 1 < H.index)
    (hpass : ∀ z : ZMod n, StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) :
    ¬n.Prime := by
  intro hp
  have ht : H = ⊤ := by
    apply (Subgroup.eq_top_iff' H).2
    intro u
    obtain ⟨v, hv, he⟩ := hpass (u : ZMod n) (strongPass_of_prime_unit hp u)
    exact (Units.ext he : v = u) ▸ hv
  exact (ne_of_gt hi) (Subgroup.index_eq_one.mpr ht)

end PseudoPrime.PrimeTest
