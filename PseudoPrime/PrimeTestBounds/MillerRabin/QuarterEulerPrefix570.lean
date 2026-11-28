/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEuler570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedLowerBound

/-! # Lower bound for the finite Euler sum in the 570 kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive indices, multiplying the cubic exponential minorant by the
nonnegative quadratic Euler factor bounds the weight by six Mangoldt moments from below. -/
private theorem moment_lower {n : ℕ} (hn : 0 < n) :
    (3 / 8 : ℝ) * quarterMangoldtMoment 0 n + (81 / 200 : ℝ) * quarterMangoldtMoment 1 n +
        (6147 / 40000 : ℝ) * quarterMangoldtMoment 2 n +
        (1701 / 200000 : ℝ) * quarterMangoldtMoment 3 n +
        (12393 / 50000000 : ℝ) * quarterMangoldtMoment 4 n +
        (23409 / 5000000000 : ℝ) * quarterMangoldtMoment 5 n ≤
      ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  let v := Real.log n
  have hv : 0 ≤ v := Real.log_natCast_nonneg n
  have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have ht := Real.sum_le_exp_of_nonneg (show 0 ≤ v * (3 / 50) by positivity) 4
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_one, Nat.cast_zero, pow_zero, pow_one, div_one, zero_add] at ht
  have hm :=
    mul_le_mul_of_nonneg_left ht
      (show
        0 ≤
          ((3 + 153 / 50 * v + 2601 / 2500 * v ^ 2) / 8) * ArithmeticFunction.vonMangoldt n *
            (n : ℝ) ^ (-(79 / 50 : ℝ))
        by positivity)
  have he : (n : ℝ) ^ (-(79 / 50 : ℝ)) * Real.exp (v * (3 / 50)) = ((n : ℝ) ^ (38 / 25 : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    dsimp only [v]
    ring
  unfold quarterMangoldtMoment quarterEulerWeight570
  rw [← div_div, div_eq_mul_inv (_ / 8) ((n : ℝ) ^ (38 / 25 : ℝ)), ← he]
  dsimp only [v] at hm ⊢
  linarith only [hm]

/-- The six certified Mangoldt moments through 2701 give a rational lower bound
for the finite Euler sum at exponent 38/25 via the cubic exponential minorant. -/
theorem quarter_euler_prefix_lower_570 :
    (7982843201259 / 2500000000000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  have h :=
    Finset.sum_le_sum (s := Finset.Ioc 0 2701) (fun n hn ↦ moment_lower (Finset.mem_Ioc.mp hn).1)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  linarith only [h, quarter_moment_lower_real0, quarter_moment_lower_real1,
    quarter_moment_lower_real2, quarter_moment_lower_real3, quarter_moment_lower_real4,
    quarter_moment_lower_real5]

/-- A lower bound on the Euler remainder beyond 2701 supplies the total-weight hypothesis
of the three-character mass estimate by adding the certified prefix. -/
theorem quarter_euler_lower_of_tail_570
    (h :
      (1335906798741 / 2500000000000 : ℝ) ≤
        (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) -
          ∑ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n) :
    37275 / 10000 ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n := by
  linarith only [h, quarter_euler_prefix_lower_570]

end PseudoPrime.PrimeTestBounds.MillerRabin
