/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Weighted prime supply through 43 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The primes through 43 used as distinct labels in the weighted family. -/
def primeSeed43Primes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]

/-- Integer logarithm weights scaled by ten for the supply through 43.
The first eight weights reuse the previous supply; larger primes share three
certified cutoff bounds. -/
def primeSeed43Weight (p : ℕ) : ℕ :=
  if p ≤ 19 then primeSeed19Weight p else if p ≤ 23 then 32 else if p ≤ 31 then 35 else 38

/-- The list of scaled weights assigned to the ordered prime labels. -/
def primeSeed43Weights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30, 30, 32, 35, 35, 38, 38, 38]

/-- The cumulative weighted-count row through budget 77. -/
def primeSeed43Row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 33, 34, 38, 44, 47, 50, 55, 61, 64, 70, 77, 84, 89, 97, 107, 114, 122, 136,
    144, 154, 169, 183, 195, 210, 229, 246, 263, 285, 307, 327, 352, 380, 406, 436, 469, 505, 537,
    577, 621, 659, 704, 759, 809]

/-- The remaining cumulative-count rows through budget 77. -/
def primeSeed43Tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 17, 17, 19, 22, 23, 24, 27, 28, 30, 32, 33, 37, 39, 42, 46, 50, 52, 59, 60,
      65, 72, 76, 81, 88, 93, 102, 109, 116, 124, 132, 142, 151, 160, 173, 184, 198, 210, 225, 241,
      253, 268, 290, 304],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 11, 11, 12, 15, 15, 16, 17, 17, 18, 19, 19, 20, 22, 23, 24, 27, 28, 32, 32, 35,
      40, 43, 44, 49, 51, 56, 59, 64, 65, 72, 77, 79, 84, 92, 96, 105, 108, 116, 125, 129, 136, 148,
      153],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 9, 9, 9, 12, 12, 13, 13, 13, 13, 14, 14, 15, 15, 16, 16, 19, 19, 21, 21, 23, 25,
      28, 28, 32, 34, 38, 40, 45, 45, 50, 54, 55, 57, 64, 64, 73, 73, 76, 82, 85, 87, 97, 97],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 8, 8, 8, 11, 11, 11, 11, 11, 11, 11, 11, 11, 11, 12, 12, 13, 13, 14, 14, 16, 16,
      19, 19, 20, 22, 25, 27, 32, 32, 36, 40, 40, 42, 48, 48, 54, 54, 55, 61, 62, 62, 69, 69],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 7, 7, 7, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 11, 11, 11, 11,
      13, 13, 14, 14, 17, 19, 21, 21, 25, 29, 29, 31, 37, 37, 43, 43, 43, 49, 49, 49, 55, 55],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 6, 6, 6, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 9, 12, 12,
      14, 14, 15, 19, 19, 21, 27, 27, 33, 33, 33, 39, 39, 39, 45, 45],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 5, 5, 5, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8, 9, 9,
      10, 10, 11, 13, 13, 15, 18, 18, 24, 24, 24, 30, 30, 30, 36, 36],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 4, 4, 4, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
      7, 7, 8, 8, 8, 10, 10, 10, 16, 16, 16, 22, 22, 22, 28, 28],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 3, 3, 3, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 9, 9, 9, 15, 15, 15, 21, 21],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 2, 2, 2, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 9, 9, 9, 15, 15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 10, 10],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 6, 6],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the recurrence for all weights and budgets. -/
theorem primeSeed43_checked :
    weightedPrimeTableCheck 77 primeSeed43Weights (primeSeed43Row :: primeSeed43Tail) = true := by
  decide +kernel

/-- The prime labels are distinct, their weights match the table, and every
weight is positive. These properties transfer the numerical table to products. -/
theorem primeSeed43_labels :
    primeSeed43Primes.Nodup ∧
      primeSeed43Primes.map primeSeed43Weight = primeSeed43Weights ∧
      ∀ p ∈ primeSeed43Primes, 0 < primeSeed43Weight p := by
  decide +kernel

/-- Every listed label is prime and does not exceed the cutoff 43. -/
theorem primeSeed43_prime_supply : ∀ p ∈ primeSeed43Primes, p.Prime ∧ p ≤ 43 := by decide +kernel

/-- Every scaled integer weight bounds the logarithm of its corresponding
prime. Rational certificates bound the new cutoff values, and monotonicity
handles primes sharing a cutoff. -/
theorem primeSeed43_weight_bounds :
    ∀ p ∈ primeSeed43Primes, Real.log p ≤ (primeSeed43Weight p : ℝ) / 10 := by
  have h23 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 23 5 16 3 (32 / 10) = true from by
          decide +kernel)).2
  have h31 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 31 5 16 3 (35 / 10) = true from by
          decide +kernel)).2
  have h43 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 43 6 16 3 (38 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h23 h31 h43
  have h29 : Real.log (29 : ℝ) ≤ (7 / 2 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (29 : ℝ) ≤ 31)).trans h31
  have h37 : Real.log (37 : ℝ) ≤ (19 / 5 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (37 : ℝ) ≤ 43)).trans h43
  have h41 : Real.log (41 : ℝ) ≤ (19 / 5 : ℝ) :=
    (Real.log_le_log (by norm_num only) (by norm_num only : (41 : ℝ) ≤ 43)).trans h43
  intro p hp
  simp only [primeSeed43Primes, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num only [primeSeed43Weight, Nat.reduceLeDiff, Nat.cast_ofNat, ite_true, ite_false]
  · exact prime_seed19_weight_bounds 2 (by decide)
  · exact prime_seed19_weight_bounds 3 (by decide)
  · exact prime_seed19_weight_bounds 5 (by decide)
  · exact prime_seed19_weight_bounds 7 (by decide)
  · exact prime_seed19_weight_bounds 11 (by decide)
  · exact prime_seed19_weight_bounds 13 (by decide)
  · exact prime_seed19_weight_bounds 17 (by decide)
  · exact prime_seed19_weight_bounds 19 (by decide)
  · exact h23
  · exact h29
  · exact h31
  · exact h37
  · exact h41
  · exact h43

/-- The weighted multiset family through budget 77 has exactly 809 members.
The table and label-invariance theorem provide its cardinality. -/
theorem primeSeed43_family_card :
    (weightedPrimeFamily primeSeed43Primes.toFinset primeSeed43Weight 77).card = 809 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed43Weight 77 primeSeed43Primes primeSeed43Weights
          primeSeed43_labels.1 primeSeed43_labels.2.2 primeSeed43_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 77 primeSeed43Weights primeSeed43Row primeSeed43Tail
          primeSeed43_checked 77 (by decide)).symm)
  change (weightedPrimeFamily primeSeed43Primes.toFinset primeSeed43Weight 77).card = 809 at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
