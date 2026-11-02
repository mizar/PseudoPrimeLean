/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part2FiniteLogBounds
public import PseudoPrime.LLS.Part1ProductFinite

/-! # Finite Part 2 witnesses from prime divisors and the existing product catalog -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a prime divisor of a nonzero modulus and any subgroup of its unit group.
Claim: that prime residue is outside the subgroup's image.
Proof: a representative unit would imply coprimality, contradicting divisibility.
Role: admit nonunit witnesses exactly as the original Part 2 conclusion permits. -/
theorem prime_dvd_outside_subgroup_image {q p : ℕ} [NeZero q] (hp : p.Prime) (hd : p ∣ q)
    (H : Subgroup (ZMod q)ˣ) : ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  rintro ⟨u, _, he⟩
  have hu : IsUnit (p : ZMod q) := he ▸ u.isUnit
  exact (hp.coprime_iff_not_dvd.mp ((ZMod.isUnit_iff_coprime p q).mp hu)) hd

/-- A checked coverage pair supplies an outside prime below any covering real cap.
Input: a nonzero modulus, coverage, a real bound for the prime cap, and a proper unit subgroup.
Claim: a prime below that bound is outside the subgroup image.
Proof: apply coverage soundness and cast the integer bound.
Role: share small finite algebraic witnesses across analytic radius comparisons. -/
theorem exists_prime_outside_image_le_of_coverage {q cap k code divisorCode : ℕ} [NeZero q]
    (hc : unitGenerationCoverCheck q cap k code divisorCode = true) {X : ℝ} (hb : (cap : ℝ) ≤ X)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) :=
  Exists.elim (exists_prime_outside_of_unitCoverage hc H hH) fun p hp ↦
    ⟨p, hp.1, (Nat.cast_le.mpr hp.2.2.1).trans hb, hp.2.2.2⟩

/-- Input: 79 <= q < 3000 and a proper subgroup of the unit group.
Claim: a prime outside the image lies at most (log q)^2, without GRH or prime exclusion.
Proof: combine the existing product catalog with the integer-cap logarithmic comparison.
Role: cover the large part of the finite extension from five. -/
theorem exists_prime_outside_part2_large_finite {q : ℕ} [NeZero q] (hq : 79 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) :=
  Exists.elim (exists_prime_outside_part1_finite_cap (le_trans (Nat.le_add_right 5 74) hq) hQ H hH)
    fun p hp ↦
    ⟨p, hp.1, (Nat.cast_le.mpr hp.2.2.1).trans (part2_catalog_cap_le_log_sq hq), hp.2.2.2⟩

end PseudoPrime.LLS
