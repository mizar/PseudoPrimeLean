/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleLogPower

/-! # Monotonicity of the quarter-square reflected moment envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The entrance radius 34 has logarithm at least three. Compare with `2^5`
and use the standard certified lower bound for `log 2`. -/
theorem quarter_log_34_lower : (3 : ℝ) ≤ Real.log 34 := by
  have h :=
    Real.log_le_log (show (0 : ℝ) < 2 ^ 5 by norm_num only) (show (2 : ℝ) ^ 5 ≤ 34 by norm_num only)
  rw [Real.log_pow] at h
  have h2 := Real.log_two_gt_d9
  norm_num only at h
  linarith only [h, h2]

/-- Every logarithmic monomial of degree at most five in the reflected moment
envelope decreases from radius 34 onward. The negative squared-radius power
outweighs the logarithmic growth. -/
theorem quarter_moment_term_antitone (m : ℕ) (hm : m ≤ 5) :
    AntitoneOn (fun r : ℝ ↦ (r ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ m)
      (Set.Ici 34) := by
  by_cases hm0 : m = 0
  · subst m
    intro x hx y hy hxy
    change (34 : ℝ) ≤ x at hx
    have hx0 : 0 < x := by linarith only [hx]
    have hxy2 := pow_le_pow_left₀ hx0.le hxy 2
    simpa only [pow_zero, mul_one] using
      Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hx0) hxy2 (by norm_num only : (-(27 / 25 : ℝ)) ≤ 0)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hk : ((k + 1 : ℕ) : ℝ) ≤ 5 := by exact_mod_cast hm
    have hbase : (0 : ℝ) ≤ 21 / 8 + 2 * Real.log 34 := by linarith only [quarter_log_34_lower]
    have hthreshold : 2 * ((k + 1 : ℕ) : ℝ) ≤ (54 / 25 : ℝ) * (21 / 8 + 2 * Real.log 34) := by
      nlinarith only [hk, quarter_log_34_lower]
    have ha :=
      refined_log_power_antitone k (b := (21 / 8 : ℝ)) (p := (54 / 25 : ℝ)) (E := 34)
        (by norm_num only) (by norm_num only) hbase hthreshold
    intro x hx y hy hxy
    have he {z : ℝ} (hz : (34 : ℝ) ≤ z) :
      (z ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (z ^ 2)) ^ (k + 1) =
        ((21 / 8 : ℝ) + 2 * Real.log z) ^ (k + 1) * z ^ (-(54 / 25 : ℝ)) := by
      have hz0 : 0 < z := by linarith only [hz]
      have hp : (z ^ 2) ^ (-(27 / 25 : ℝ)) = z ^ (-(54 / 25 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
        norm_num only
      rw [hp, Real.log_pow]
      norm_num only
      ring
    change
      (y ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (y ^ 2)) ^ (k + 1) ≤
        (x ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (x ^ 2)) ^ (k + 1)
    rw [he hx, he hy]
    exact ha hx hy hxy

/-- The reflected moment polynomial, multiplied by its negative scale power,
decreases from radius 34 onward. Each of its six nonnegative monomials decreases. -/
theorem quarter_moment_scale_antitone :
    AntitoneOn
      (fun r : ℝ ↦
        (r ^ 2) ^ (-(27 / 25 : ℝ)) * quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log (r ^ 2)))
      (Set.Ici 34) := by
  intro x hx y hy hxy
  have h0 := quarter_moment_term_antitone 0 (by decide) hx hy hxy
  have h1 := quarter_moment_term_antitone 1 (by decide) hx hy hxy
  have h2 := quarter_moment_term_antitone 2 (by decide) hx hy hxy
  have h3 := quarter_moment_term_antitone 3 (by decide) hx hy hxy
  have h4 := quarter_moment_term_antitone 4 (by decide) hx hy hxy
  have h5 := quarter_moment_term_antitone 5 (by decide) hx hy hxy
  dsimp only [quarterMomentPolynomial]
  ring_nf at h0 h1 h2 h3 h4 h5 ⊢
  linarith only [h0, h1, h2, h3, h4, h5]

/-- The conductor contribution decreases from radius 34 onward. Its logarithmic
fifth power grows more slowly than the accompanying negative power. -/
theorem quarter_conductor_antitone :
    AntitoneOn (fun r : ℝ ↦ r * (r ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (r ^ 2)) ^ 5)
      (Set.Ici 34) := by
  have hb : (10 : ℝ) ≤ (29 / 25 : ℝ) * (21 / 8 + 2 * Real.log (34 : ℝ)) := by
    linarith only [quarter_log_34_lower]
  have ha :=
    refined_log_fifth_antitone (b := (21 / 8 : ℝ)) (p := (29 / 25 : ℝ)) (E := (34 : ℝ))
      (by norm_num only) (by norm_num only) hb
  intro x hx y hy hxy
  have he {z : ℝ} (hz : (34 : ℝ) ≤ z) :
    z * (z ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (z ^ 2)) ^ 5 =
      ((21 / 8 : ℝ) + 2 * Real.log z) ^ 5 * z ^ (-(29 / 25 : ℝ)) := by
    have hz0 : 0 < z := by linarith only [hz]
    have hr : (z ^ 2) ^ (-(27 / 25 : ℝ)) = z ^ (-(54 / 25 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]
      norm_num only
    have hr' : z * z ^ (-(54 / 25 : ℝ)) = z ^ (-(29 / 25 : ℝ)) := by
      calc
        _ = z ^ (1 : ℝ) * z ^ (-(54 / 25 : ℝ)) := by rw [Real.rpow_one]
        _ = z ^ (1 + (-(54 / 25 : ℝ))) := (Real.rpow_add hz0 _ _).symm
        _ = _ := by norm_num only
    rw [hr, hr', Real.log_pow]
    norm_num only
    ring
  change
    y * (y ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (y ^ 2)) ^ 5 ≤
      x * (x ^ 2) ^ (-(27 / 25 : ℝ)) * ((21 / 8 : ℝ) + Real.log (x ^ 2)) ^ 5
  rw [he hx, he hy]
  exact ha hx hy hxy

end PseudoPrime.PrimeTestBounds.MillerRabin
