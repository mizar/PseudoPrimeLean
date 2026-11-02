/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCatalog
public import PseudoPrime.LLS.Part1ProductSoundness
public import PseudoPrime.LLS.UnitGenerationCoverSoundness

/-! # Finite algebraic extraction from the independent LLS catalog

This module retrieves checked code pairs and outside-prime witnesses without a real bound or
GRH. Analytic consumers compare the integer cap with their own radius in separate modules.
Finite blocks must not import this proof layer or the catalog assembly.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Every modulus from five to 2999 has a checked catalog certificate pair.
Input: the finite lower and upper bounds. Claim: some product and divisor codes pass coverage.
Proof: use abstract block extraction with the concrete catalog.
Role: share finite certification independently of analytic transfer. -/
theorem exists_part1_catalog_coverage {q : ℕ} (hq : 5 ≤ q) (hQ : q < 3000) :
    ∃ code divisorCode : ℕ,
      unitGenerationCoverCheck q (part1PrimeCap q) (q.log2 + 1) code divisorCode = true :=
  exists_part1_coverage_of_blocks part1ProductCodeBlock part1DivisorCodeBlock
    part1ProductCatalog_checks hq hQ

/-- The catalog gives an outside prime below the selected integer cap.
Input: a nonzero modulus from five to 2999 and a proper subgroup of its unit group.
Claim: a prime not dividing the modulus lies below the cap and outside the subgroup image.
Proof: extract a checked pair and apply coverage soundness.
Role: the common finite algebraic input to Part 1, Part 2, and later radius comparisons. -/
theorem exists_prime_outside_part1_finite_cap {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ p ≤ part1PrimeCap q ∧ ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) :=
  Exists.elim (exists_part1_catalog_coverage hq hQ) fun _code h ↦
    Exists.elim h fun _divisorCode hc ↦ exists_prime_outside_of_unitCoverage hc H hH

end PseudoPrime.LLS
