/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBases
public import PseudoPrime.PrimeTest.MillerRabin.AGP.FiniteBasesIff
public import PseudoPrime.PrimeTest.MillerRabin.AGP.InitialBasesUnbounded
public import PseudoPrime.AnalyticNumberTheory.AGP.UnconditionalProgressionCountData

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
Input: `h` gives, for every pair of natural bounds, a Carmichael number passing
all positive bases up to the first bound and exceeding the second.

Claim: every finite set of prime bases has a Carmichael number passing all its bases.

Content: the supremum of the finite set bounds each member, while primality makes
each member a positive base.

Proof: apply `h` with both bounds equal to `S.sup id`, then use `Finset.le_sup`.

Role: this is the logical reduction from `AGPInitialBasesUnbounded` to
`AGPFinitePrimeBases`; the analytic construction of the former remains separate.
-/
private theorem agp_finite_prime_bases_of_initial
    (h : AGPInitialBasesUnbounded) : AGPFinitePrimeBases := by
  apply agpFinitePrimeBases_iff.mpr
  have hDep := agpInitialBasesUnbounded_iff.mp h
  intro S hS
  let B : ℕ := S.sup id
  obtain ⟨a, _, haCar, haPass⟩ := hDep B B
  refine ⟨a, haCar, ?_⟩
  intro p hp
  have hp_le : p ≤ B := by
    simpa [B] using (Finset.le_sup (s := S) (f := id) hp)
  exact haPass p (Nat.Prime.pos (hS p hp)) hp_le

/--
For any finite set of prime bases, there exists a Carmichael number
that passes the strong Miller-Rabin test at every base in the set.

This theorem is unconditional.
-/
theorem agp_finite_prime_bases :
    AGPFinitePrimeBases :=
  agp_finite_prime_bases_of_initial agp_initial_bases_unbounded

end PseudoPrime.PrimeTest.MillerRabin.AGP
