/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Statement
public import PseudoPrime.NumberTheory.JacobiCharacterPrimeEvaluation
public import PseudoPrime.NumberTheory.JacobiWitness.Basic
public import PseudoPrime.NumberTheory.CharacterModulus

/-!
# From the LLS character bound to a Jacobi witness

The prime supplied by `LLS.llsTheorem11S1Character` for the quadratic character at level `4 * n` is
an odd
prime with Jacobi value `-1`.  Minimality then transfers the explicit LLS bound to
`PseudoPrime.NumberTheory.primeNegOneWitness`.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/--
For odd nonsquare `n` with character modulus `4 * n ≥ 3000`, the assumed LLS S1 bound
produces an odd prime with Jacobi value `-1` within its corrected logarithmic-square radius.
The proof applies the character theorem at level `4 * n` and converts nontrivial character
evaluation to membership in `PrimeNegOneWitnessSet n`. This supplies the least-witness bound.
-/
theorem exists_primeNegOneWitness_of_LLS (hLLS : LLS.llsTheorem11S1Character) (n : ℕ) (hn : Odd n)
    (hns : ¬IsSquare n) (hq : 3000 ≤ NumberTheory.characterModulus n) :
    ∃ ℓ : ℕ,
      ℓ ∈ NumberTheory.PrimeNegOneWitnessSet n ∧
        (ℓ : ℝ) ≤
          (Real.log (NumberTheory.characterModulus n : ℝ) +
              LLS.llsCorrectionTerm (NumberTheory.characterModulus n)) ^
            2 := by
  let _ : NeZero (4 * n) := ⟨Nat.mul_ne_zero (by norm_num only) (Odd.pos hn).ne'⟩
  obtain ⟨ℓ, hℓprime, hℓndvd, hℓchar, hℓbound⟩ :=
    hLLS (4 * n) (NumberTheory.complexQuadraticCharacter n hn)
      (by simpa only [NumberTheory.characterModulus] using hq)
      (NumberTheory.complexQuadraticCharacter_ne_one_of_not_square n hn hns)
  have hℓmem :=
    NumberTheory.primeNegOneWitness_mem_of_complexQuadraticCharacter_ne_one n hn hℓprime hℓndvd
      hℓchar
  exact ⟨ℓ, hℓmem, by simpa only [NumberTheory.characterModulus] using hℓbound⟩

/--
Assuming the LLS S1 character bound, odd nonsquare `n`, `4 * n ≥ 3000`, and witness-set
nonemptiness `hw`, the least odd-prime Jacobi `-1` witness is bounded by the corrected LLS
radius. Minimality bounds it by the prime from `exists_primeNegOneWitness_of_LLS`; casting
and transitivity give the real estimate used by the elementary-radius envelope.
-/
theorem primeNegOneWitness_le_of_LLS (hLLS : LLS.llsTheorem11S1Character) (n : ℕ) (hn : Odd n)
    (hns : ¬IsSquare n) (hq : 3000 ≤ NumberTheory.characterModulus n)
    (hw : (NumberTheory.PrimeNegOneWitnessSet n).Nonempty) :
    (NumberTheory.primeNegOneWitness n hw : ℝ) ≤
      (Real.log (NumberTheory.characterModulus n : ℝ) +
          LLS.llsCorrectionTerm (NumberTheory.characterModulus n)) ^
        2 := by
  obtain ⟨ℓ, hℓmem, hℓbound⟩ := exists_primeNegOneWitness_of_LLS hLLS n hn hns hq
  exact (Nat.cast_le.mpr (NumberTheory.primeNegOneWitness_le n hw hℓmem)).trans hℓbound

end PseudoPrime.PseudoSquare
