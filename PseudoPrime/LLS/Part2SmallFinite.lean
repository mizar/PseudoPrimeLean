/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part2FiniteTransfer

/-! # Small-modulus Part 2 witnesses checked by the kernel -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a local index i, corresponding to q=5+i.
Output: below 79, accept a prime divisor within the small cap or the existing generation code;
return true on padding indices. Role: certify nonunit and unit witnesses with one exact check. -/
def part2SmallLeaf (i : ℕ) : Bool :=
  let q := 5 + i
  if q < 79 then
    NumberTheory.generationPrimeLabels.any (fun p ↦ decide (p ≤ part2SmallPrimeCap q ∧ p ∣ q)) ||
      NumberTheory.generationProductCheck q (part2SmallPrimeCap q) (q.log2 + 1)
        SmallPart1.block00Codes[i]!
  else true

/-- Input: one of five windows of sixteen indices.
Claim: every leaf of the window passes the exact small certificate check.
Proof: kernel computation with default resources. Role: cover q from 5 through 78. -/
theorem part2_small_windows (j : Fin 5) :
    NumberTheory.generationBalancedAll part2SmallLeaf 4 (16 * j.val) = true := by
  fin_cases j
  all_goals decide +kernel

/-- Input: 5 <= q < 79.
Claim: the corresponding prime-divisor or product-generation check succeeds.
Proof: choose the checked window by quotient and remainder and remove padding.
Role: extract one finite check without enumerating subgroups. -/
theorem part2_small_leaf_sound {q : ℕ} (hq : 5 ≤ q) (hQ : q < 79) :
    (NumberTheory.generationPrimeLabels.any (fun p ↦ decide (p ≤ part2SmallPrimeCap q ∧ p ∣ q)) ||
        NumberTheory.generationProductCheck q (part2SmallPrimeCap q) (q.log2 + 1)
          SmallPart1.block00Codes[q - 5]!) =
      true := by
  let i := q - 5
  have hs : 5 + i = q := Nat.add_sub_of_le hq
  have hj : i / 16 < 5 :=
    (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 16)).mpr (by linarith only [hs, hQ])
  have hl : 16 * (i / 16) ≤ i := by simpa only [Nat.mul_comm] using Nat.div_mul_le_self i 16
  have hu : i < 16 * (i / 16) + 2 ^ 4 := by
    have hm := Nat.mod_lt i (by decide +kernel : 0 < 16)
    have he := Nat.mod_add_div i 16
    norm_num only
    linarith only [hm, he]
  have hc := NumberTheory.generationBalancedAll_sound (part2_small_windows ⟨i / 16, hj⟩) hl hu
  simp only [part2SmallLeaf] at hc
  rw [hs, ite_eq_left hQ] at hc
  exact hc

/-- Input: 5 <= q < 79 and any proper unit subgroup.
Claim: a prime outside its image is at most (log q)^2, without GRH or prime exclusion.
Proof: use the checked small prime divisor or generation branch and the cap comparison.
Role: complete the bottom finite range for Part 2. -/
theorem exists_prime_outside_part2_small_finite {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 79)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (p : ZMod q) := by
  rcases Bool.or_eq_true_iff.mp (part2_small_leaf_sound hq hQ) with hd | hg
  · obtain ⟨p, hp, hpd⟩ := List.any_eq_true.mp hd
    have h := of_decide_eq_true hpd
    have hprime := NumberTheory.generationPrimeLabels_prime hp
    exact
      ⟨p, hprime, (Nat.cast_le.mpr h.1).trans (part2_small_cap_le_log_sq hq),
        prime_dvd_outside_subgroup_image hprime h.2 H⟩
  · exact
      exists_prime_outside_image_le_of_product hg (modulus_le_product_depth (NeZero.ne q))
        (part2_small_cap_le_log_sq hq) H hH

end PseudoPrime.LLS
