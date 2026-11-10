/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareThird
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028NineCount
import PseudoPrime.PrimeTestBounds.MillerRabin.SignedPrimeProductTransfer

/-! # Extended square-factor weighted count -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cumulative weighted-product counts through budget 140. -/
private def row : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 24, 26, 28, 31, 32, 36, 39, 42, 45, 50, 54, 57, 63, 67, 72, 77, 85, 90, 97, 105, 114,
    120, 130, 140, 149, 159, 171, 183, 195, 210, 224, 239, 254, 272, 288, 307, 327, 347, 368, 392,
    418, 441, 470, 497, 527, 557, 593, 626, 663, 702, 744, 784, 830, 878, 926, 976, 1031, 1088,
    1146, 1210, 1276, 1343, 1413, 1489, 1566, 1647, 1733, 1821, 1913, 2010, 2114, 2217, 2330, 2443,
    2564, 2687, 2821, 2955, 3098, 3246, 3403, 3560, 3729, 3904, 4085, 4271, 4469, 4673, 4885, 5107,
    5338, 5575, 5822, 6080, 6347, 6624, 6914, 7212, 7522, 7844, 8182, 8525, 8888, 9258, 9647, 10045,
    10465, 10892, 11341]

/-- Suffix counts used to verify the weighted-product recurrence. -/
private def tail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 12, 13, 14, 15, 15, 17, 17, 18, 19, 22, 23, 25, 27, 28, 30, 32, 35, 36, 40, 42, 47, 48,
      53, 55, 59, 62, 66, 69, 75, 80, 84, 90, 95, 101, 105, 112, 117, 123, 129, 138, 146, 153, 163,
      170, 180, 189, 201, 208, 222, 232, 247, 257, 273, 285, 300, 313, 329, 344, 362, 380, 398, 417,
      437, 458, 478, 501, 523, 545, 570, 597, 625, 651, 683, 710, 743, 774, 811, 841, 881, 916, 960,
      996, 1042, 1083, 1130, 1173, 1223, 1270, 1325, 1378, 1434, 1490, 1551, 1611, 1674, 1739, 1807,
      1874, 1947, 2022, 2102, 2178, 2264, 2344, 2435, 2523, 2621, 2710, 2816],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 8, 8, 9, 9, 9, 10, 10, 10, 11, 12, 12, 13, 14, 14, 15, 17, 18, 19, 22, 23, 25, 25, 28, 28,
      31, 32, 34, 34, 39, 40, 42, 43, 47, 48, 50, 53, 55, 57, 60, 63, 66, 69, 73, 75, 79, 84, 89,
      91, 99, 103, 109, 111, 120, 122, 130, 133, 140, 143, 154, 158, 166, 170, 180, 185, 193, 201,
      210, 216, 226, 235, 245, 253, 266, 273, 285, 296, 310, 318, 336, 346, 363, 371, 391, 400, 420,
      430, 449, 459, 484, 497, 518, 530, 555, 569, 591, 609, 634, 651, 677, 697, 724, 744, 774, 793,
      824, 849, 882, 903, 942],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 7, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8, 8, 9, 9, 10, 10, 11, 11, 14, 14, 16, 16, 18, 18, 21, 21,
      22, 22, 26, 26, 28, 28, 30, 30, 31, 31, 32, 32, 35, 35, 38, 38, 41, 41, 45, 45, 49, 49, 56,
      56, 61, 61, 67, 67, 73, 73, 77, 77, 85, 85, 91, 91, 96, 96, 102, 102, 107, 107, 115, 115, 123,
      123, 133, 133, 142, 142, 152, 152, 166, 166, 178, 178, 190, 190, 204, 204, 214, 214, 231, 231,
      245, 245, 259, 259, 273, 273, 288, 288, 306, 306, 324, 324, 344, 344, 365, 365, 385, 385,
      412],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 11, 11, 14, 14, 15, 15,
      18, 18, 20, 20, 21, 21, 21, 21, 21, 21, 21, 21, 22, 22, 23, 23, 24, 24, 27, 27, 30, 30, 33,
      33, 37, 37, 42, 42, 45, 45, 50, 50, 53, 53, 55, 55, 57, 57, 58, 58, 59, 59, 62, 62, 66, 66,
      69, 69, 75, 75, 81, 81, 87, 87, 94, 94, 102, 102, 107, 107, 116, 116, 122, 122, 126, 126, 131,
      131, 136, 136, 140, 140, 146, 146, 154, 154, 161, 161, 171, 171, 181],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 8, 8, 9, 9, 12, 12,
      14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 16, 16, 16, 16, 18, 18, 19,
      19, 22, 22, 24, 24, 29, 29, 32, 32, 34, 34, 35, 35, 35, 35, 35, 35, 35, 35, 36, 36, 36, 36,
      38, 38, 39, 39, 42, 42, 44, 44, 49, 49, 52, 52, 59, 59, 64, 64, 67, 67, 69, 69, 70, 70, 71,
      71, 71, 71, 73, 73, 74, 74, 77, 77, 79],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 7, 7,
      9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 10, 14, 14, 17, 17, 19, 19, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20,
      20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 25, 25, 29, 29, 32, 32, 34, 34, 35, 35, 35, 35,
      35, 35, 35, 35, 35, 35, 35, 35, 35],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4,
      5, 5, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 8,
      8, 9, 9, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10, 10,
      10, 10, 10, 11, 11, 12, 12, 13, 13, 14, 14, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 15,
      15],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2,
      2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3,
      3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

private theorem checked :
    weightedPrimeTableCheck 140 target028NineWeights (row :: tail) = true := by decide +kernel

-- Reducing the final entry of the 141-element count row exceeds the default depth.
set_option maxRecDepth 8192 in
private theorem family_card :
    (weightedPrimeFamily target028NinePrimes.toFinset target028NineWeight 140).card = 11341 := by
  have h :=
    (weightedPrimeCount_weights_eq_card target028NineWeight 140 target028NinePrimes
          target028NineWeights target028Nine_labels.1 target028Nine_labels.2.2
          target028Nine_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 140 target028NineWeights row tail checked 140
          (by decide)).symm)
  exact h

set_option maxHeartbeats 800000 in
-- The weighted nine-prime family exceeds the default heartbeat limit.
/-- A prime square divisor on logarithmic scales 9.6 through 20 supplies a
quarter-square rejecting prime. Factors through 2292 use the preceding bound;
the remaining factors use a checked family of 11341 signed-product pairs. -/
theorem quarter_square_fourth {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (48 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hp390 : p ≤ 2292
  · exact quarter_square_factor_le2292 hn ho hp hdiv hL hp390
  · have hp391 : 2293 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hp390)
    have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
    have hB : (23 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    have hcert :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 514473124 30 64 20 21 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
    have hnle : n ≤ 514473124 := by
      have hlog : Real.log (n : ℝ) ≤ Real.log (514473124 : ℝ) := hU.trans hcert
      exact_mod_cast
        (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
              (by norm_num only : (0 : ℝ) < 514473124)).mp
          hlog
    have hpsq : p ^ 2 ≤ 514473124 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
    have hp2292 : p ≤ 22682 := by nlinarith only [hpsq]
    let S := target028NinePrimes.toFinset
    let w := target028NineWeight
    let F := weightedPrimeFamily S w 140
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.1
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 140 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 140 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 140 hwpos T).mp hT).2
    have hc : F.card = 11341 := by
      have h := family_card
      change F.card = 11341 at h
      exact h
    have hcount : p - 1 < 2 * F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp2292
    have h391 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 2293 12 32 (77 / 10) 8 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h391
    have hlogp := Real.log_le_log (by norm_num only : (0 : ℝ) < 2293) (Nat.cast_le.mpr hp391)
    have hbudget : Real.log 2 + (140 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9, h391, hlogp]
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_signed hn ho hp hp2 (by decide : 0 < 2) hdiv S F 23 140 w 10
        (by norm_num only) hsub hprime hbound hw hcost hbudget hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
