/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCheck
public import PseudoPrime.LLS.UnitGenerationCheckSoundness

/-! # Finite extraction from checked LLS Part 1 blocks

This module selects a modulus certificate from sixteen-entry windows and abstract 128-entry
blocks. Concrete catalog data and analytic transfer are assembled after this finite interface.
The chosen counts and range belong to LLS's certificate representation.

Keep this proof layer outside the computational imports of finite blocks. Adding or changing
proofs, catalog imports or analytic dependencies here must not trigger their expensive checks.
In particular, this abstract extraction module must not import the concrete catalog.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- The quotient by sixteen selects one of eight windows and locates the original index.
Input: an index below 128. Claim: its window number is below eight and its interval contains it.
Proof: quotient/remainder bounds. Role: avoid duplicating arithmetic in certificate extraction. -/
private theorem part1_window_bounds {i : ℕ} (hi : i < 128) :
    i / 16 < 8 ∧ 16 * (i / 16) ≤ i ∧ i < 16 * (i / 16) + 2 ^ 4 := by
  exact
    ⟨(Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 15)).mpr hi,
      le_of_eq_of_le (Nat.mul_comm 16 (i / 16)) (Nat.div_mul_le_self i 16),
      lt_of_eq_of_lt (Nat.div_add_mod i 16).symm
        (Nat.add_lt_add_left (Nat.mod_lt i (Nat.zero_lt_succ 15)) _)⟩

/-- Checked windows supply the product-and-divisor certificate at any in-range local index.
Input: all eight sixteen-entry checks, an index below 128 and a modulus below 3000.
Claim: the corresponding executable coverage check succeeds.
Proof: select the containing window and unfold its leaf. Role: abstract finite block extraction. -/
theorem part1_product_block_sound {start i : ℕ} {codes divisorCodes : Array ℕ}
    (hc :
      ∀ j : Fin 8,
        unitGenerationAll (part1ProductLeaf start codes divisorCodes) 4 (16 * j.val) = true)
    (hi : i < 128) (hq : start + i < 3000) :
    unitGenerationCoverCheck (start + i) (part1PrimeCap (start + i)) (Nat.log2 (start + i) + 1)
        codes[i]! divisorCodes[i]! =
      true := by
  rcases part1_window_bounds hi with ⟨hj, hl, hu⟩
  have h := unitGenerationAll_sound (hc ⟨i / 16, hj⟩) hl hu
  simpa only [part1ProductLeaf, ite_eq_left hq] using h

/-- Abstract checked blocks yield a certificate pair for each modulus from five to 2999.
Input: two arrays per block and all eight window checks in each of twenty-four blocks.
Claim: some product code and divisor code pass the coverage check at the requested modulus.
Proof: division and remainder select its block and index. Role: catalog-independent extraction. -/
theorem exists_part1_coverage_of_blocks (codes divisorCodes : Fin 24 → Array ℕ)
    (hc :
      ∀ b : Fin 24,
        ∀ j : Fin 8,
          unitGenerationAll (part1ProductLeaf (5 + 128 * b.val) (codes b) (divisorCodes b)) 4
              (16 * j.val) =
            true)
    {q : ℕ} (hq : 5 ≤ q) (hQ : q < 3000) :
    ∃ code divisorCode : ℕ,
      unitGenerationCoverCheck q (part1PrimeCap q) (q.log2 + 1) code divisorCode = true := by
  let r := q - 5
  have hs : r + 5 = q := Nat.sub_add_cancel hq
  have hb : r / 128 < 24 :=
    (Nat.div_lt_iff_lt_mul (Nat.zero_lt_succ 127)).mpr
      (lt_of_le_of_lt (Nat.sub_le q 5) (lt_trans hQ (by decide +kernel)))
  have hi : r % 128 < 128 := Nat.mod_lt r (Nat.zero_lt_succ 127)
  have he : 5 + 128 * (r / 128) + r % 128 = q := by
    rw [Nat.add_assoc, Nat.div_add_mod, Nat.add_comm, hs]
  have hcheck :=
    part1_product_block_sound (hc ⟨r / 128, hb⟩) hi
      (show 5 + 128 * (r / 128) + r % 128 < 3000 by
        rw [he]
        exact hQ)
  rw [he] at hcheck
  exact ⟨_, _, hcheck⟩

end PseudoPrime.LLS
