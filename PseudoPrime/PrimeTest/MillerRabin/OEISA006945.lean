module

public import Mathlib.Data.Nat.MaxPowDiv
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Data.ZMod.Basic

/-!
# OEIS A006945 https://oeis.org/A006945
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
An odd composite number passing the strong Miller-Rabin
test at the first n prime bases (0-indexed).
-/
noncomputable def A006945Candidate (n a : ℕ) : Prop :=
  let (s, d) := Nat.maxPowDvdDiv 2 (a - 1)
  1 < a ∧
    Odd a ∧
    ¬Nat.Prime a ∧
    ∀ k < n,
      (Nat.nth Nat.Prime k : ZMod a) ^ d = 1 ∨
        ∃ j < s, (Nat.nth Nat.Prime k : ZMod a) ^ (2 ^ j * d) = -1

/--
The n-th term of OEIS A006945 is the least
odd composite passing the first n prime bases (0-indexed).
-/
noncomputable def IsA006945Term (n a : ℕ) : Prop :=
  IsLeast {b : ℕ | A006945Candidate n b} a

end PseudoPrime.PrimeTest
