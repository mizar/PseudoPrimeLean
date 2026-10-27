/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1SmallRadiusBounds
public import PseudoPrime.NumberTheory.UnitGenerationProducts
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Compact product-certificate transfer for the original LLS Part 1 bound -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a modulus q. Definition: cap 19 below 705 and cap 43 otherwise.
Output: a natural prime cap.
Role: compare compact generation certificates with the original radius. -/
def llsPart1FinitePrimeCap (q : ℕ) : ℕ :=
  if q < 705 then 19 else 43

/-- Input: a block start, exact integer codes and a local index.
Definition: check product generation at the corresponding modulus below 3000;
indices beyond the target range impose no condition.
Output: a Boolean. Role: pad the last finite certificate block without adding moduli. -/
def llsPart1ProductLeaf (start : ℕ) (codes : Array ℕ) (i : ℕ) : Bool :=
  if start + i < 3000 then
    NumberTheory.generationProductCheck (start + i) (llsPart1FinitePrimeCap (start + i))
      ((start + i).log2 + 1) codes[i]!
  else true

/-- Input: q >= 5. Claim: the selected finite prime cap lies within the original Part 1 bound.
Proof: split at 705 and use the two certified analytic cap comparisons.
Role: keep finite group generation independent of logarithmic computation. -/
theorem lls_part1_finite_cap_le_radius {q : ℕ} (hq : 5 ≤ q) :
    (llsPart1FinitePrimeCap q : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  by_cases h : q < 705
  · simpa only [llsPart1FinitePrimeCap, ite_eq_left h, Nat.cast_ofNat] using
      lls_part1_radius_sq_ge_nineteen (show 4 ≤ q by linarith only [hq])
  · simpa only [llsPart1FinitePrimeCap, ite_eq_right h, Nat.cast_ofNat] using
      lls_part1_radius_sq_ge_forty_three (Nat.le_of_not_gt h)

/-- Input: eight checked windows of sixteen leaves, an index below 128 and a target below 3000.
Claim: the corresponding product certificate passes.
Proof: select the window using division by sixteen and use balanced-check soundness.
Role: permit small source modules and default kernel resource limits. -/
theorem lls_part1_product_block_sound {start i : ℕ} {codes : Array ℕ}
    (hc :
      ∀ j : Fin 8,
        NumberTheory.generationBalancedAll (llsPart1ProductLeaf start codes) 4 (16 * j.val) = true)
    (hi : i < 128) (hq : start + i < 3000) :
    NumberTheory.generationProductCheck (start + i) (llsPart1FinitePrimeCap (start + i))
        ((start + i).log2 + 1) codes[i]! =
      true := by
  have hj : i / 16 < 8 := (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 16)).mpr hi
  have hl : 16 * (i / 16) ≤ i := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self i 16
  have hu : i < 16 * (i / 16) + 2 ^ 4 := by
    have hm := Nat.mod_lt i (by decide +kernel : 0 < 16)
    have he := Nat.mod_add_div i 16
    norm_num only
    linarith only [hm, he]
  have h := NumberTheory.generationBalancedAll_sound (hc ⟨i / 16, hj⟩) hl hu
  simpa only [llsPart1ProductLeaf, ite_eq_left hq] using h

/-- Input: a nonzero modulus. Claim: q <= 2^(log2(q)+1).
Proof: a larger modulus would contradict the defining logarithm bound.
Role: guarantee that the product mask includes every unit representative. -/
theorem modulus_le_product_depth {q : ℕ} (hq : q ≠ 0) : q ≤ 2 ^ (q.log2 + 1) := by
  apply Nat.le_of_lt
  by_contra hn
  have hh := (Nat.le_log2 hq).mpr (Nat.le_of_not_gt hn)
  exact Nat.not_succ_le_self q.log2 hh

/-- Input: q >= 5, a checked product code and a proper unit subgroup.
Claim: an outside prime lies within the exact original LLS Part 1 radius, without GRH.
Proof: transfer group generation, construct the witness unit and compare the finite cap.
Role: discharge the finite premise of the entrance-from-three assembly theorem. -/
theorem exists_prime_outside_lls_part1_of_product {q code : ℕ} [NeZero q] (hq : 5 ≤ q)
    (hc : NumberTheory.generationProductCheck q (llsPart1FinitePrimeCap q) (q.log2 + 1) code = true)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  obtain ⟨p, hp, hd, hb, hout⟩ :=
    NumberTheory.exists_prime_outside_of_generationProductCheck hc
      (modulus_le_product_depth (NeZero.ne q)) H hH
  let u := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hd)
  have hu : (u : ZMod q) = (p : ZMod q) := ZMod.coe_unitOfCoprime _ _
  have hn : u ∉ H := fun h ↦ hout ⟨u, h, hu⟩
  exact ⟨p, ⟨hp, hd, u, hn, hu⟩, (Nat.cast_le.mpr hb).trans (lls_part1_finite_cap_le_radius hq)⟩

/-- Input: twenty-four code blocks with all eight windows checked in each block.
Claim: every modulus 5 <= q < 3000 has an outside prime within the original LLS radius.
Proof: select the block and local index by division, then use generation soundness.
Role: separate the full finite-range proof from the representation of certificate data. -/
theorem exists_prime_outside_lls_part1_of_catalog (codes : Fin 24 → Array ℕ)
    (hc :
      ∀ b : Fin 24,
        ∀ j : Fin 8,
          NumberTheory.generationBalancedAll (llsPart1ProductLeaf (5 + 128 * b.val) (codes b)) 4
              (16 * j.val) =
            true)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (Real.log q + llsCorrectionTerm q) ^ 2 := by
  let r := q - 5
  have hs : r + 5 = q := Nat.sub_add_cancel hq
  have hb : r / 128 < 24 :=
    (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 128)).mpr (by linarith only [hs, hQ])
  have hi : r % 128 < 128 := Nat.mod_lt r (by decide +kernel : 0 < 128)
  have he : 5 + 128 * (r / 128) + r % 128 = q := by
    have hd := Nat.mod_add_div r 128
    linarith only [hd, hs]
  have hcheck :=
    lls_part1_product_block_sound (hc ⟨r / 128, hb⟩) hi
      (show 5 + 128 * (r / 128) + r % 128 < 3000 by
        rw [he]; exact hQ)
  rw [he] at hcheck
  exact exists_prime_outside_lls_part1_of_product hq hcheck H hH

end PseudoPrime.LLS
