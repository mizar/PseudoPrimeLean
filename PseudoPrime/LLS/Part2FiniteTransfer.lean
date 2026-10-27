/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part2FiniteLogBounds
public import PseudoPrime.LLS.Part1FromThree

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

/-- Input: a checked product-generation code, complete residue coverage,
a real upper bound for its prime cap and a proper unit subgroup.
Claim: a prime below that bound lies outside the subgroup's image.
Proof: use generation soundness and transport the integer cap.
Role: provide a radius-independent finite witness interface. -/
theorem exists_prime_outside_image_le_of_product {q cap k code : ℕ} [NeZero q]
    (hc : NumberTheory.generationProductCheck q cap k code = true) (hdepth : q ≤ 2 ^ k) {X : ℝ}
    (hb : (cap : ℝ) ≤ X) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨p, hp, _, hcap, hout⟩ :=
    NumberTheory.exists_prime_outside_of_generationProductCheck hc hdepth H hH
  exact ⟨p, hp, (Nat.cast_le.mpr hcap).trans hb, hout⟩

/-- Input: 5 <= q < 3000.
Claim: some existing catalog code passes the product-generation check at q.
Proof: locate the block and its sixteen-leaf window using division and remainder.
Role: reuse the checked catalog independently of Part 1's analytic correction. -/
theorem exists_part1_catalog_product_check {q : ℕ} (hq : 5 ≤ q) (hQ : q < 3000) :
    ∃ code : ℕ,
      NumberTheory.generationProductCheck q (llsPart1FinitePrimeCap q) (q.log2 + 1) code =
        true := by
  let r := q - 5
  have hs : r + 5 = q := Nat.sub_add_cancel hq
  have hb : r / 128 < 24 :=
    (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 128)).mpr (by linarith only [hs, hQ])
  have hi : r % 128 < 128 := Nat.mod_lt r (by decide +kernel : 0 < 128)
  have he : 5 + 128 * (r / 128) + r % 128 = q := by
    have hd := Nat.mod_add_div r 128
    linarith only [hd, hs]
  have hcheck :=
    lls_part1_product_block_sound (SmallPart1.part1_catalog_checks ⟨r / 128, hb⟩) hi
      (show 5 + 128 * (r / 128) + r % 128 < 3000 by
        rw [he]; exact hQ)
  rw [he] at hcheck
  exact ⟨_, hcheck⟩

/-- Input: 79 <= q < 3000 and a proper subgroup of the unit group.
Claim: a prime outside the image lies at most (log q)^2, without GRH or prime exclusion.
Proof: combine the existing product catalog with the integer-cap logarithmic comparison.
Role: cover the large part of the finite extension from five. -/
theorem exists_prime_outside_part2_large_finite {q : ℕ} [NeZero q] (hq : 79 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  obtain ⟨code, hc⟩ :=
    exists_part1_catalog_product_check (le_trans (by decide +kernel : 5 ≤ 79) hq) hQ
  exact
    exists_prime_outside_image_le_of_product hc (modulus_le_product_depth (NeZero.ne q))
      (part2_catalog_cap_le_log_sq hq) H hH

end PseudoPrime.LLS
