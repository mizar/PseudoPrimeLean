/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.ZMod.Units

/-!
# Bounded prime coverage of unit residues

An integer cap is retained independently of the modulus. This allows a certified
coverage result to be transferred to a divisor before a real bound is applied.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Every unit residue modulo `m` has a prime representative at most `M`.
The integer cap is independent of the modulus and no minimality is required.
This preserves the witness bound when finite coverage is reused for divisors. -/
def BoundedPrimeResidueCoverage (m M : ℕ) : Prop :=
  ∀ a : (ZMod m)ˣ, ∃ p : ℕ, p.Prime ∧ (p : ZMod m) = (a : ZMod m) ∧ p ≤ M

/-- An integer representing a unit modulo `m` represents its image modulo a divisor `d`.
Apply the quotient ring homomorphism to the equality and simplify the natural cast.
This transports prime witnesses without repeating their congruence checks. -/
theorem natCast_eq_unitsMap_of_eq {d m p : ℕ} (hd : d ∣ m) (a : (ZMod m)ˣ)
    (he : (p : ZMod m) = (a : ZMod m)) : (p : ZMod d) = (ZMod.unitsMap hd a : ZMod d) := by
  have hc := congrArg (ZMod.castHom hd (ZMod d)) he
  simpa only [ZMod.castHom_apply, ZMod.cast_natCast hd, ZMod.unitsMap_val] using hc

/-- Bounded prime coverage modulo a nonzero `m` transfers to any divisor `d`
with the same integer cap. Lift each target unit through the surjective units map,
then project the supplied prime witness. This shares one finite coverage proof
among several target moduli before their separate real bounds are applied. -/
theorem BoundedPrimeResidueCoverage.of_dvd {d m M : ℕ} [NeZero m] (hd : d ∣ m)
    (h : BoundedPrimeResidueCoverage m M) : BoundedPrimeResidueCoverage d M := by
  intro a
  obtain ⟨b, hb⟩ := ZMod.unitsMap_surjective hd a
  obtain ⟨p, hp, he, hM⟩ := h b
  refine ⟨p, hp, ?_, hM⟩
  exact (natCast_eq_unitsMap_of_eq hd b he).trans (congrArg (fun u : (ZMod d)ˣ ↦ (u : ZMod d)) hb)

/-- Increasing the integer cap preserves bounded prime coverage.
Keep each prime and congruence witness and compose its bound with `M ≤ N`.
This allows a transferred certificate to fit a target modulus's admissible cap. -/
theorem BoundedPrimeResidueCoverage.mono {m M N : ℕ} (h : BoundedPrimeResidueCoverage m M)
    (hMN : M ≤ N) : BoundedPrimeResidueCoverage m N := by
  intro a
  obtain ⟨p, hp, he, hM⟩ := h a
  exact ⟨p, hp, he, hM.trans hMN⟩

end PseudoPrime.NumberTheory
