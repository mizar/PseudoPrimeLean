module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.CarmichaelNumber

/-!
Alford-Granville-Pomerance

Alford–Granville–Pomerance (1994), "On the difficulty of finding reliable witnesses"
proves that for any finite set of prime bases, there are infinitely many
Carmichael numbers that pass all of their Miller–Rabin tests.
https://math.dartmouth.edu/~carlp/PDF/reliable.pdf
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
Alford-Granville-Pomerance:
For every finite set of prime bases, there exists a Carmichael
number passing the strong Miller-Rabin test at every base
in that set.
-/
def AGPFinitePrimeBases : Prop :=
  ∀ S : Finset ℕ,
    (∀ p ∈ S, Nat.Prime p) →
      ∃ a : ℕ,
        Nat.IsCarmichael a ∧
          ∀ p ∈ S,
            let (s, d) := Nat.maxPowDvdDiv 2 (a - 1)
            (p : ZMod a) ^ d = 1 ∨ ∃ j < s, (p : ZMod a) ^ (2 ^ j * d) = -1

/--
For every B and C, there exists a Carmichael number
greater than C that passes the strong Miller-Rabin
test at every positive base up to B.

This theorem is unconditional.
-/
def AGPInitialBasesUnbounded : Prop :=
  ∀ B C : ℕ,
    ∃ a : ℕ,
      C < a ∧
        Nat.IsCarmichael a ∧
          ∀ b : ℕ,
            0 < b →
              b ≤ B →
                let (s, d) := Nat.maxPowDvdDiv 2 (a - 1)
                (b : ZMod a) ^ d = 1 ∨ ∃ j < s, (b : ZMod a) ^ (2 ^ j * d) = -1

end PseudoPrime.PrimeTest.MillerRabin.AGP
