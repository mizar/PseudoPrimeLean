/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import PseudoPrime.LLS.ParityRationalWitnessProfiles

/-! # Transferring finite generation certificates to the parity profile

Proper subgroups omit an eligible prime from every valid generation tree.
The analytic profile exceeds seven for q ≥ 3 and eighty-one for q ≥ 8,
so uniform integer caps suffice for the finite small-modulus extension.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- A valid generation tree at a nonzero modulus gives an outside prime through cap.
Assume all eligible prime residues belong to H and use generation to contradict H proper.
No GRH or analytic premise is needed for this finite algebraic result. -/
theorem exists_prime_outside_of_generation_tree {q cap : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode}
    (hvalid : NumberTheory.UnitGenerationTreeValid q cap tree) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ p ≤ cap := by
  classical
  by_contra hn
  apply hH
  apply NumberTheory.subgroup_eq_top_of_valid_generation_tree hvalid H
  intro p hp hd hb u hu
  by_contra hout
  exact hn ⟨p, ⟨hp, hd, u, hout, hu⟩, hb⟩

/-- At a nonzero modulus with a valid tree and proper H, the least outside prime is at most cap.
Minimize the unbounded outside-prime predicate and compare it with the bounded witness.
Minimality ranges over every coprime outside prime. -/
theorem exists_least_prime_outside_of_generation_tree {q cap : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode}
    (hvalid : NumberTheory.UnitGenerationTreeValid q cap tree) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ p ≤ cap ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_of_generation_tree hvalid H hH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.find_min' hex hp).trans hb, fun _ hr =>
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS
