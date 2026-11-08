/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaOneSided

/-! # Sixth logarithmic moment for the 0.28 Euler bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For each positive integer, the logarithm is at most `100/27` times its
tenth power. The tangent bound for the exponential and `exp 1 > 27/10`
retain the factor of `e` needed for the high-range Euler certificate. -/
theorem target028_log_le_tenth_power (n : ℕ) :
    Real.log n ≤ (100 / 27 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, Real.zero_rpow (by norm_num only : (1 / 10 : ℝ) ≠ 0),
      mul_zero, le_refl]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have he : (27 / 10 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have ht := Real.add_one_le_exp (Real.log n / 10 - 1)
    have hm := mul_le_mul_of_nonneg_right ht (Real.exp_pos 1).le
    have hE : Real.exp (Real.log n / 10 - 1) * Real.exp 1 = (n : ℝ) ^ (1 / 10 : ℝ) := by
      rw [← Real.exp_add, Real.rpow_def_of_pos hn0]
      congr 1
      ring
    rw [hE] at hm
    have hlow := mul_le_mul_of_nonneg_right he hl
    nlinarith only [hlow, hm]

/-- Bound the sixth logarithmic summand by a first logarithmic summand at
exponent `27/25`, choosing the power `1/10` to improve the scalar budget. -/
theorem target028_log_six_reduction (n : ℕ) :
    (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ)) ≤
      (100 / 27 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(27 / 25 : ℝ))) := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, zero_pow (by decide : 6 ≠ 0), zero_mul, mul_zero,
      le_refl]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hb := target028_log_le_tenth_power n
    have hp := pow_le_pow_left₀ hlog hb 5
    have hnneg : 0 ≤ (n : ℝ) ^ (-(79 / 50 : ℝ)) := Real.rpow_nonneg hnpos.le _
    have h := mul_le_mul_of_nonneg_right hp (mul_nonneg hlog hnneg)
    have hscale :
      ((n : ℝ) ^ (1 / 10 : ℝ)) ^ 5 * (n : ℝ) ^ (-(79 / 50 : ℝ)) = (n : ℝ) ^ (-(27 / 25 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnpos.le, ← Real.rpow_add hnpos]
      congr 1
      norm_num only
    have heq :
      ((100 / 27 : ℝ) * (n : ℝ) ^ (1 / 10 : ℝ)) ^ 5 * (Real.log n * (n : ℝ) ^ (-(79 / 50 : ℝ))) =
        (100 / 27 : ℝ) ^ 5 * (Real.log n * (n : ℝ) ^ (-(27 / 25 : ℝ))) := by
      rw [div_pow, div_eq_mul_inv, ← hscale]
      norm_num only
      ring
    rw [heq] at h
    convert h using 1
    ring

/-- The sixth logarithmic series has a rational upper bound using the exponent
`27/25`. Summability and the existing first-logarithm integral bound justify the comparison. -/
theorem target028_log_six_bound :
    (∑' n : ℕ, (Real.log n) ^ 6 * (n : ℝ) ^ (-(79 / 50 : ℝ))) ≤
      (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27) := by
  have he := Analysis.summable_logPower_envelope (r := 2 / 25) (by norm_num only)
  have he' : Summable (fun n : ℕ ↦ (Real.log n + 1) * (n : ℝ) ^ (-(27 / 25 : ℝ))) := by
    convert he using 1
    norm_num only
  have hs : Summable (fun n : ℕ ↦ Real.log n * (n : ℝ) ^ (-(27 / 25 : ℝ))) := by
    refine Summable.of_nonneg_of_le ?_ ?_ he'
    · intro n
      exact mul_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    · intro n
      exact
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have ht :=
    (refined_log_power_summable 6).tsum_le_tsum target028_log_six_reduction
      (hs.mul_left ((100 / 27 : ℝ) ^ 5))
  have hb := Analysis.tsum_logPower_le (r := 2 / 25) (by norm_num only)
  have hb' : (∑' n : ℕ, Real.log n * (n : ℝ) ^ (-(27 / 25 : ℝ))) ≤ (25 / 2 : ℝ) ^ 2 + 25 / 27 := by
    norm_num only [show -(2 / 25 : ℝ) - 1 = -(27 / 25 : ℝ) by norm_num only,
      show (2 / 25 : ℝ)⁻¹ = 25 / 2 by norm_num only,
      show (2 / 25 : ℝ) + 1 = 27 / 25 by norm_num only,
      show (27 / 25 : ℝ)⁻¹ = 25 / 27 by norm_num only] at hb ⊢
    exact hb
  rw [tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left hb' (by positivity))

/-- The reflected principal Euler term is bounded using the improved sixth
logarithmic moment. This bound retains the exact scale dependence needed at
the high-range entrance. -/
theorem target028_reflected_euler_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * 16 *
        x ^ (-(27 / 25 : ℝ)) *
        (((21 / 8 : ℝ) + Real.log x) ^ 5 * ((50 / 29 : ℝ) ^ 2 + 50 / 79) +
          (100 / 27 : ℝ) ^ 5 * ((25 / 2 : ℝ) ^ 2 + 25 / 27)) := by
  apply (refined_reflected_one_explicit hx).trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add le_rfl target028_log_six_bound
  · positivity

end PseudoPrime.PrimeTestBounds.MillerRabin
