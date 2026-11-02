/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductBlock23
public import PseudoPrime.LLS.Part1CoverageTransfer

/-! # Integration of the final independent LLS Part 1 block

This test consumes the concrete final block through finite extraction and analytic transfer.
It covers every in-range local position and any proper unit subgroup, retaining the original
LLS radius without GRH. Padding positions are excluded by the explicit upper bound.
-/

@[expose] public section

namespace PseudoPrime.Tests

/-- The final block supplies an outside prime within the original LLS radius.
Input: an index below 128 with modulus below 3000, and a proper subgroup of its unit group.
Claim: the concrete certificate yields an eligible prime within the squared original radius.
Proof: extract its checked window and apply analytic transfer.
Role: validate the concrete block-to-witness interface before assembling all twenty-four blocks. -/
theorem part1_block23_original_radius {i : ℕ} [NeZero (2949 + i)] (hi : i < 128)
    (hq : 2949 + i < 3000) (H : Subgroup (ZMod (2949 + i))ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      LLS.PrimeOutsideSubgroup (2949 + i) H p ∧
        (p : ℝ) ≤ (Real.log (2949 + i : ℕ) + LLS.llsCorrectionTerm (2949 + i)) ^ 2 := by
  have hc := LLS.part1_product_block_sound LLS.part1Product23_checks hi hq
  exact
    LLS.exists_prime_outside_part1_of_coverage
      (le_trans (Nat.le_add_right 5 2944) (Nat.le_add_right 2949 i)) hc H hH

end PseudoPrime.Tests
