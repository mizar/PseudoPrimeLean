module

public import Mathlib.NumberTheory.PrimeCounting
public import PseudoPrime.PrimeTest.MillerRabin.OEISA006945Iff
public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBasesTheorem

/-!
# OEIS A006945 https://oeis.org/A006945 Exists
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
For every n, there exists an odd composite number passing
the strong Miller-Rabin test at the first n prime bases
(0-indexed).

This is an unconditional consequence of the
Alford-Granville-Pomerance theorem on strong pseudoprimes
to arbitrary finite sets of prime bases.
-/
theorem exists_a006945_candidate_of_agp (hAGP : MillerRabin.AGP.AGPFinitePrimeBases) (n : ℕ) :
    ∃ a : ℕ, A006945Candidate n a := by
  let S : Finset ℕ := (Finset.range n).image (Nat.nth Nat.Prime)
  have hS : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
    exact Nat.prime_nth_prime k
  have hAGPWithDecomposition := MillerRabin.AGP.agpFinitePrimeBases_iff.mp hAGP
  obtain ⟨a, haCarmichael, haPass⟩ := hAGPWithDecomposition S hS
  have ha1 : 1 < a := lt_trans (by decide : 1 < 2) haCarmichael.two_lt
  refine ⟨a, (a006945Candidate_iff n a).mpr ?_⟩
  refine ⟨ha1, haCarmichael.odd, haCarmichael.not_prime, ?_⟩
  intro k hk
  have hmem : Nat.nth Nat.Prime k ∈ S := by
    exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk, rfl⟩
  exact haPass _ hmem

/--
For every n, there exists an odd composite number passing
the strong Miller-Rabin test at the first n prime bases
(0-indexed).

This is an unconditional consequence of the
Alford-Granville-Pomerance theorem on strong pseudoprimes
to arbitrary finite sets of prime bases.
-/
theorem exists_a006945_candidate (n : ℕ) : ∃ a : ℕ, A006945Candidate n a :=
  exists_a006945_candidate_of_agp MillerRabin.AGP.agp_finite_prime_bases n

/--
Every term of OEIS A006945 exists (0-indexed).
-/
theorem exists_a006945_term (n : ℕ) : ∃ a : ℕ, IsA006945Term n a := by
  classical
  obtain ⟨a, ha⟩ := exists_a006945_candidate n
  let h : ∃ b : ℕ, A006945Candidate n b := ⟨a, ha⟩
  exact ⟨Nat.find h, Nat.isLeast_find h⟩

end PseudoPrime.PrimeTest
