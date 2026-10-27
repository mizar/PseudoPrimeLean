module

public import PseudoPrime.PrimeTest.MillerRabin.OEISA006945
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition

/-!
# OEIS A006945 https://oeis.org/A006945
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Equivalence between A006945Candidate and the existing
strong Miller-Rabin pass predicate.
-/
theorem a006945Candidate_iff (n a : ℕ) :
    A006945Candidate n a ↔
      1 < a ∧
        Odd a ∧ ¬Nat.Prime a ∧ ∀ k < n, StrongMillerRabinPass a (Nat.nth Nat.Prime k : ZMod a) := by
  rfl

end PseudoPrime.PrimeTest
