/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed43

/-! # Weighted prime supply through 61 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The primes through 61 as distinct labels extending the supply through 43. -/
def target030Seed61Primes : List ℕ :=
  target030Seed43Primes ++ [47, 53, 59, 61]

/-- Integer logarithm weights scaled by ten for the supply through 61. The
previous weights are preserved and each new prime has a certified upper bound. -/
def target030Seed61Weight (p : ℕ) : ℕ :=
  if p ≤ 43 then target030Seed43Weight p
  else if p ≤ 47 then 39 else if p ≤ 53 then 40 else if p ≤ 59 then 41 else 42

/-- The ordered list of scaled weights for the prime supply through 61. -/
def target030Seed61Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38, 39, 40, 41, 42]

/-- The cumulative weighted-count row through budget 96. -/
def target030Seed61Row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 33, 34, 38, 44, 48, 52, 58, 65, 68, 74, 81, 89, 95, 104, 115, 123, 132, 147,
    157, 168, 184, 200, 214, 231, 253, 273, 293, 318, 344, 368, 397, 430, 461, 496, 535, 579, 619,
    668, 721, 770, 825, 892, 958, 1024, 1101, 1183, 1263, 1352, 1447, 1550, 1651, 1765, 1892, 2015,
    2149, 2304, 2455, 2614, 2790, 2979, 3169, 3376]

/-- The remaining cumulative-count rows through budget 96. -/
def target030Seed61Tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 17, 17, 19, 22, 24, 26, 30, 32, 34, 36, 37, 41, 43, 46, 50, 55, 58, 66, 68,
      73, 80, 85, 91, 99, 106, 116, 125, 134, 144, 154, 166, 177, 188, 203, 217, 235, 251, 271, 291,
      309, 329, 357, 379, 405, 433, 462, 493, 527, 555, 592, 627, 664, 709, 752, 797, 857, 905, 963,
      1025, 1087, 1154, 1227],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 11, 11, 12, 15, 16, 18, 20, 21, 22, 23, 23, 24, 26, 27, 28, 31, 32, 36, 36, 39,
      44, 48, 50, 56, 60, 66, 70, 76, 78, 86, 93, 97, 103, 112, 118, 129, 135, 146, 157, 165, 175,
      191, 202, 217, 230, 245, 258, 276, 284, 301, 318, 335, 352, 373, 392, 424, 443, 470, 498, 532,
      562, 600],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 9, 9, 9, 12, 13, 15, 16, 17, 17, 18, 18, 19, 19, 20, 20, 23, 23, 25, 25, 27, 29,
      32, 32, 36, 39, 44, 47, 53, 54, 60, 66, 69, 72, 80, 82, 93, 96, 102, 109, 115, 119, 131, 136,
      147, 154, 167, 172, 183, 187, 198, 206, 217, 223, 238, 246, 267, 278, 295, 307, 330, 345,
      370],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 8, 8, 8, 11, 12, 13, 14, 15, 15, 15, 15, 15, 15, 16, 16, 17, 17, 18, 18, 20, 20,
      23, 23, 24, 26, 29, 31, 36, 37, 42, 48, 50, 53, 60, 62, 70, 73, 77, 84, 88, 90, 99, 104, 111,
      115, 123, 125, 130, 133, 138, 140, 148, 151, 158, 164, 174, 182, 193, 198, 215, 226, 239],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 7, 7, 7, 10, 11, 12, 13, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 15, 15, 15, 15,
      17, 17, 18, 18, 21, 23, 25, 25, 29, 34, 35, 38, 45, 47, 55, 58, 61, 68, 71, 73, 81, 86, 91,
      95, 100, 102, 106, 107, 109, 109, 112, 114, 116, 116, 124, 129, 133, 136, 145, 153, 162],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 6, 6, 6, 9, 10, 11, 12, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13, 13,
      13, 13, 13, 13, 16, 16, 18, 18, 19, 23, 23, 25, 31, 33, 41, 44, 47, 54, 57, 59, 67, 72, 76,
      80, 85, 87, 89, 90, 91, 91, 91, 91, 91, 91, 95, 95, 98, 98, 100, 106, 107],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 5, 5, 5, 8, 9, 10, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12,
      12, 12, 12, 13, 13, 14, 14, 15, 17, 17, 19, 22, 23, 30, 32, 34, 41, 44, 46, 54, 59, 63, 67,
      72, 74, 76, 77, 78, 78, 78, 78, 78, 78, 79, 79, 80, 80, 81, 83, 84],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 4, 4, 4, 7, 8, 9, 10, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11,
      11, 11, 11, 11, 11, 11, 11, 12, 12, 12, 14, 14, 14, 20, 21, 22, 29, 32, 34, 42, 47, 51, 55,
      60, 62, 64, 65, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 66, 67],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 3, 3, 3, 6, 7, 8, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 13, 13, 13, 19, 21, 23, 31, 36, 40, 44,
      49, 51, 53, 54, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55, 55],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 2, 2, 2, 5, 6, 7, 8, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9,
      9, 9, 9, 9, 9, 9, 9, 9, 10, 10, 10, 13, 14, 15, 22, 26, 30, 34, 39, 41, 43, 44, 45, 45, 45,
      45, 45, 45, 45, 45, 45, 45, 45, 45, 45],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 4, 5, 6, 7, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8,
      8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 14, 17, 21, 25, 30, 32, 34, 35, 36, 36, 36, 36, 36,
      36, 36, 36, 36, 36, 36, 36, 36],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 3, 4, 5, 6, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 10, 12, 15, 18, 22, 24, 26, 27, 28, 28, 28, 28, 28,
      28, 28, 28, 28, 28, 28, 28, 28],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 8, 10, 12, 15, 17, 19, 20, 21, 21, 21, 21, 21,
      21, 21, 21, 21, 21, 21, 21, 21],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 7, 9, 11, 13, 14, 15, 15, 15, 15, 15, 15,
      15, 15, 15, 15, 15, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 6, 8, 9, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted-count recurrence. -/
theorem target030Seed61_checked :
    weightedPrimeTableCheck 96 target030Seed61Weights (target030Seed61Row :: target030Seed61Tail) =
      true := by
  decide +kernel

/-- The labels are distinct, their weights match the table, and every weight
is positive. This transfers the checked recurrence to repeated prime products. -/
theorem target030Seed61_labels :
    target030Seed61Primes.Nodup ∧
      target030Seed61Primes.map target030Seed61Weight = target030Seed61Weights ∧
      ∀ p ∈ target030Seed61Primes, 0 < target030Seed61Weight p := by
  decide +kernel

/-- Every listed label is prime and is at most 61. -/
theorem target030Seed61_prime_supply : ∀ p ∈ target030Seed61Primes, p.Prime ∧ p ≤ 61 := by
  decide +kernel

/-- The scaled integer weights dominate the logarithms of their prime labels.
The existing supply handles primes through 43; rational certificates handle
the four new primes. -/
theorem target030Seed61_weight_bounds :
    ∀ p ∈ target030Seed61Primes, Real.log p ≤ (target030Seed61Weight p : ℝ) / 10 := by
  have h47 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 47 6 16 3 (39 / 10) = true from by
          decide +kernel)).2
  have h53 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 53 6 16 3 (40 / 10) = true from by
          decide +kernel)).2
  have h59 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59 6 16 4 (41 / 10) = true from by
          decide +kernel)).2
  have h61 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 61 6 16 4 (42 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h47 h53 h59 h61
  intro p hp
  simp only [target030Seed61Primes, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with hp | rfl | rfl | rfl | rfl
  · have hp43 := (target030Seed43_prime_supply p hp).2
    simpa only [target030Seed61Weight, ite_eq_left hp43] using target030Seed43_weight_bounds p hp
  · norm_num only [target030Seed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h47
  · norm_num only [target030Seed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h53
  · norm_num only [target030Seed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h59
  · norm_num only [target030Seed61Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
    exact h61

end PseudoPrime.PrimeTestBounds.MillerRabin
