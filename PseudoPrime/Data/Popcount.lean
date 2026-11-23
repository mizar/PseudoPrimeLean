/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Init.Data.BitVec.Basic
import Init.Data.Nat.Bitwise.Lemmas

/-! # Parallel population count for 32-bit and 64-bit words -/

public section

namespace PseudoPrime.Data

/-- Sum the lowest `n` base-`b` digits by successive remainder and division. -/
private def digitSum (b : Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, x => x % b + digitSum b n (x / b)

/-- Count the set bits by inspecting all 32 binary digits, starting at the low bit. -/
def popcount32Naive (x : BitVec 32) : Nat :=
  digitSum 2 32 x.toNat

/-- Count the set bits by inspecting all 64 binary digits, starting at the low bit. -/
def popcount64Naive (x : BitVec 64) : Nat :=
  digitSum 2 64 x.toNat

/-- Add adjacent lanes in parallel. The mask selects the low lane of each pair. -/
private def merge (x mask k : Nat) : Nat :=
  Nat.add (Nat.land x mask) (Nat.land (Nat.shiftRight x k) mask)

private theorem merge_eq (x mask k : Nat) : merge x mask k = (x &&& mask) + ((x >>> k) &&& mask) :=
  rfl

/-- Count the set bits of a 32-bit word by five parallel additions of adjacent lanes. -/
def popcount32 (x : BitVec 32) : Nat :=
  let x := merge x.toNat 0x55555555 1
  let x := merge x 0x33333333 2
  let x := merge x 0x0f0f0f0f 4
  let x := merge x 0x00ff00ff 8
  merge x 0x0000ffff 16

/-- Count the set bits of a 64-bit word by six parallel additions of adjacent lanes. -/
def popcount64 (x : BitVec 64) : Nat :=
  let x := merge x.toNat 0x5555555555555555 1
  let x := merge x 0x3333333333333333 2
  let x := merge x 0x0f0f0f0f0f0f0f0f 4
  let x := merge x 0x00ff00ff00ff00ff 8
  let x := merge x 0x0000ffff0000ffff 16
  merge x 0x00000000ffffffff 32

/-- Select the low `k` bits of each of `n` pairs of lanes. -/
private def laneMask (k : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (2 ^ k - 1) + 2 ^ (k + k) * laneMask k n

/-- The alternating mask separates into the first selected digit and the higher lane pairs. -/
private theorem splitMask (k n x : Nat) :
    x &&& laneMask k (n + 1) = x % 2 ^ k + 2 ^ (k + k) * ((x / 2 ^ (k + k)) &&& laneMask k n) := by
  let b := 2 ^ (k + k)
  have hlt : 2 ^ k - 1 < b :=
    Nat.lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos k) Nat.zero_lt_one)
      (Nat.pow_le_pow_right (by decide) (Nat.le_add_right k k))
  have hlo : laneMask k (n + 1) % b = 2 ^ k - 1 := by
    rw [laneMask, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  have hhi : laneMask k (n + 1) / b = laneMask k n := by
    rw [laneMask, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]
  have upper : (x &&& laneMask k (n + 1)) / b = (x / b &&& laneMask k n) := by
    simpa only [Nat.shiftRight_eq_div_pow, hhi, b] using
      (Nat.shiftRight_and_distrib (a := x) (b := laneMask k (n + 1)) (i := k + k))
  have low : (x &&& laneMask k (n + 1)) % b = x % 2 ^ k := by
    rw [Nat.and_mod_two_pow, hlo, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (Nat.le_add_right k k))]
  exact (Nat.mod_add_div _ b).symm.trans (by rw [low, upper])

/-- Moving past a pair and shifting to its high digit commute. -/
private theorem div_comm (x b c : Nat) : x / b / c = x / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm b c, ← Nat.div_div_eq_div_mul]

/-- Splitting the two masks isolates the first pair sum and the remaining word. -/
private theorem merge_succ (x k n : Nat) :
    merge x (laneMask k (n + 1)) k =
      (x % 2 ^ k + (x / 2 ^ k) % 2 ^ k) +
        2 ^ (k + k) * merge (x / 2 ^ (k + k)) (laneMask k n) k := by
  simp only [merge_eq, splitMask, Nat.shiftRight_eq_div_pow, Nat.mul_add]
  rw [div_comm x (2 ^ k) (2 ^ (k + k))]
  ac_rfl

/-- Pair sums fit in the doubled lane and preserve the sum of the represented digits. -/
private theorem merge_digits (k n x : Nat) (hk : 2 ≤ 2 ^ k) :
    digitSum (2 ^ (k + k)) n (merge x (laneMask k n) k) = digitSum (2 ^ k) (n + n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n
    ih =>
    have fit : x % 2 ^ k + x / 2 ^ k % 2 ^ k < 2 ^ (k + k) := by
      rw [Nat.pow_add]
      exact
        Nat.lt_of_lt_of_le
          (Nat.add_lt_add (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k)))
          (by
            rw [← Nat.two_mul]; exact Nat.mul_le_mul_right (2 ^ k) hk)
    have size : n + 1 + (n + 1) = (n + n) + 1 + 1 := by rw [Nat.succ_add, Nat.add_succ]
    rw [size, digitSum, merge_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt fit,
      Nat.add_mul_div_left _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt fit, Nat.zero_add, ih,
      digitSum, digitSum, Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.add_assoc]

/-- A single final pair produces a value strictly below the doubled lane radix. -/
private theorem last_merge (x k : Nat) (hk : 2 ≤ 2 ^ k) :
    digitSum (2 ^ (k + k)) 1 (merge x (2 ^ k - 1) k) = merge x (2 ^ k - 1) k := by
  have bound : merge x (2 ^ k - 1) k < 2 ^ (k + k) := by
    rw [merge_eq, Nat.and_two_pow_sub_one_eq_mod, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_add]
    exact
      Nat.lt_of_lt_of_le
        (Nat.add_lt_add (Nat.mod_lt _ (Nat.two_pow_pos k)) (Nat.mod_lt _ (Nat.two_pow_pos k)))
        (by
          rw [← Nat.two_mul]; exact Nat.mul_le_mul_right _ hk)
  rw [digitSum, digitSum, Nat.add_zero, Nat.mod_eq_of_lt bound]

/-- For every 32-bit word, each SWAR stage preserves the sum of its binary digits. -/
theorem popcount32_eq_naive (x : BitVec 32) : popcount32 x = popcount32Naive x := by
  let a := x.toNat
  let v1 := merge a 0x55555555 1
  let v2 := merge v1 0x33333333 2
  let v3 := merge v2 0x0f0f0f0f 4
  let v4 := merge v3 0x00ff00ff 8
  let v5 := merge v4 0x0000ffff 16
  change v5 = digitSum 2 32 a
  calc
    _ = digitSum (2 ^ 32) 1 v5 := (last_merge v4 16 (by decide)).symm
    _ = digitSum (2 ^ 16) 2 v4 := merge_digits 16 1 v4 (by decide)
    _ = digitSum (2 ^ 8) 4 v3 := merge_digits 8 2 v3 (by decide)
    _ = digitSum (2 ^ 4) 8 v2 := merge_digits 4 4 v2 (by decide)
    _ = digitSum (2 ^ 2) 16 v1 := merge_digits 2 8 v1 (by decide)
    _ = digitSum (2 ^ 1) 32 a := merge_digits 1 16 a (by decide)

/-- For every 64-bit word, each SWAR stage preserves the sum of its binary digits. -/
theorem popcount64_eq_naive (x : BitVec 64) : popcount64 x = popcount64Naive x := by
  let a := x.toNat
  let v1 := merge a 0x5555555555555555 1
  let v2 := merge v1 0x3333333333333333 2
  let v3 := merge v2 0x0f0f0f0f0f0f0f0f 4
  let v4 := merge v3 0x00ff00ff00ff00ff 8
  let v5 := merge v4 0x0000ffff0000ffff 16
  let v6 := merge v5 0x00000000ffffffff 32
  change v6 = digitSum 2 64 a
  calc
    _ = digitSum (2 ^ 64) 1 v6 := (last_merge v5 32 (by decide)).symm
    _ = digitSum (2 ^ 32) 2 v5 := merge_digits 32 1 v5 (by decide)
    _ = digitSum (2 ^ 16) 4 v4 := merge_digits 16 2 v4 (by decide)
    _ = digitSum (2 ^ 8) 8 v3 := merge_digits 8 4 v3 (by decide)
    _ = digitSum (2 ^ 4) 16 v2 := merge_digits 4 8 v2 (by decide)
    _ = digitSum (2 ^ 2) 32 v1 := merge_digits 2 16 v1 (by decide)
    _ = digitSum (2 ^ 1) 64 a := merge_digits 1 32 a (by decide)

/-- Count the set bits at positions below `n` by appending one bit at a time. -/
def bitCountPrefix : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, z => bitCountPrefix n z + (if z.testBit n then 1 else 0)

/-- Removing the low bit shifts every index in the remaining prefix down by one. -/
private theorem prefix_low (n z : Nat) :
    bitCountPrefix (n + 1) z = z % 2 + bitCountPrefix n (z / 2) := by
  induction n with
  | zero =>
    rcases Nat.mod_two_eq_zero_or_one z with h | h
    · rw [bitCountPrefix, bitCountPrefix, bitCountPrefix, Nat.testBit_zero, h]
      rfl
    · rw [bitCountPrefix, bitCountPrefix, bitCountPrefix, Nat.testBit_zero, h]
      rfl
  | succ n ih =>
    change bitCountPrefix (n + 1) z + _ = z % 2 + (bitCountPrefix n (z / 2) + _)
    rw [ih, Nat.testBit_div_two, Nat.add_assoc]

/-- Binary digit division and indexed bit inspection count the same prefix. -/
private theorem digits_eq_prefix (n z : Nat) : digitSum 2 n z = bitCountPrefix n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => rw [digitSum, ih, prefix_low]

/-- The SWAR result is the number of set positions among the 64 bits of the input. -/
theorem popcount64_eq_prefix (x : BitVec 64) : popcount64 x = bitCountPrefix 64 x.toNat :=
  (popcount64_eq_naive x).trans (digits_eq_prefix 64 x.toNat)

end PseudoPrime.Data
