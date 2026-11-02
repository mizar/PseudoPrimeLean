/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCheck
public import PseudoPrime.LLS.Part1ProductSoundness
public import PseudoPrime.LLS.UnitGenerationCoverSoundness
public import PseudoPrime.LLS.Part1SmallRadiusBounds
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Analytic transfer of finite LLS Part 1 coverage

This module compares the finite integer cap with the original LLS radius and transfers a
checked coverage certificate to a prime outside a proper subgroup. It contains no concrete
catalog data. Finite blocks must not import this analytic proof layer: changing analytic
estimates or unrelated declarations here must not invalidate their expensive kernel checks.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The finite prime cap fits the original LLS radius for every modulus at least five.
Input: a natural modulus at least five. Claim: its selected cap is below the squared radius.
Proof: split at 705 and use the certified bounds for nineteen and forty-three.
Role: connect integer coverage certificates to the original analytic Part 1 bound. -/
theorem part1_cap_le_radius {q : ℕ} (hq : 5 ≤ q) :
    (part1PrimeCap q : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  by_cases h : q < 705
  · simpa only [part1PrimeCap, ite_eq_left h, Nat.cast_ofNat] using
      lls_part1_radius_sq_ge_nineteen (le_trans (Nat.le_succ 4) hq)
  · simpa only [part1PrimeCap, ite_eq_right h, Nat.cast_ofNat] using
      lls_part1_radius_sq_ge_forty_three (Nat.le_of_not_gt h)

/-- A successful finite coverage certificate gives a prime within the original LLS radius.
Input: a nonzero modulus at least five, checked codes, and a proper subgroup of its unit group.
Claim: a prime outside the subgroup lies below the squared original radius, without GRH.
Proof: transfer coverage to an integer-cap witness and compare that cap with the radius.
Role: the analytic interpretation of the independent finite catalog. -/
theorem exists_prime_outside_part1_of_coverage {q code divisorCode : ℕ} [NeZero q] (hq : 5 ≤ q)
    (hc : unitGenerationCoverCheck q (part1PrimeCap q) (q.log2 + 1) code divisorCode = true)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  obtain ⟨p, hp, hd, hb, hout⟩ := exists_prime_outside_of_unitCoverage hc H hH
  let u := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hd)
  have hu : (u : ZMod q) = (p : ZMod q) := ZMod.coe_unitOfCoprime _ _
  have hn : u ∉ H := fun h ↦ hout ⟨u, h, hu⟩
  exact ⟨p, ⟨hp, hd, u, hn, hu⟩, (Nat.cast_le.mpr hb).trans (part1_cap_le_radius hq)⟩

/-- A checked family of finite blocks yields the original finite LLS Part 1 witness.
Input: twenty-four code pairs with checked windows, a modulus from five to 2999, and a proper
unit subgroup. Claim: an outside prime lies within the original squared radius, without GRH.
Proof: extract the code pair and apply analytic transfer. Role: assemble the concrete catalog. -/
theorem exists_prime_outside_part1_of_blocks (codes divisorCodes : Fin 24 → Array ℕ)
    (hc :
      ∀ b : Fin 24,
        ∀ j : Fin 8,
          unitGenerationAll (part1ProductLeaf (5 + 128 * b.val) (codes b) (divisorCodes b)) 4
              (16 * j.val) =
            true)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  obtain ⟨code, divisorCode, hcheck⟩ := exists_part1_coverage_of_blocks codes divisorCodes hc hq hQ
  exact exists_prime_outside_part1_of_coverage hq hcheck H hH

end PseudoPrime.LLS
