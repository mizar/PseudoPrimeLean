/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleTranslatedSeries

/-! # Uniform bound for the translated even digamma correction -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The exponential damping at the left endpoint of the translated window
is the reciprocal radius times a geometric factor in the pole index. -/
private theorem shifted_pole_decay {r : ℝ} (hr : 287 ≤ r) (n : ℕ) :
    Real.exp (-(2 * (1 / 4 + n)) * (2 * Real.log r)) ≤ r⁻¹ * (1 / 10 : ℝ) ^ n := by
  have hp : 0 < r := by linarith only [hr]
  have he : Real.exp (-(2 * (1 / 4 + n)) * (2 * Real.log r)) = r⁻¹ * (r ^ 4)⁻¹ ^ n := by
    rw [show -(2 * (1 / 4 + (n : ℝ))) * (2 * Real.log r) = -Real.log r + n * (-(4 * Real.log r)) by
        ring,
      Real.exp_add, Real.exp_natCast_mul, Real.exp_neg, Real.exp_log hp, Real.exp_neg,
      show (4 : ℝ) * Real.log r = Real.log (r ^ 4) by
        rw [Real.log_pow]; norm_num only,
      Real.exp_log (pow_pos hp _)]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hp.le)
  apply pow_le_pow_left₀ (inv_nonneg.mpr (pow_nonneg hp.le _))
  rw [← one_div (r ^ 4)]
  apply (one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 10) _)
  exact (by norm_num only : (10 : ℝ) ≤ 287 ^ 4).trans (pow_le_pow_left₀ (by norm_num only) hr 4)

/-- The squared exponential factor sharpens the first pole; the larger
denominators alone give the same bound at all later poles. -/
private theorem shifted_pole_coefficient (n : ℕ) :
    Real.pi / (4 * (1 / 4 + n) ^ 2) * (1 - Real.exp (-(5 * (1 / 4 + n)))) ^ 2 ≤
      (9 / 4) * Real.pi := by
  have hz : 0 ≤ 1 - Real.exp (-(5 * (1 / 4 + (n : ℝ)))) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
  cases n with
  | zero =>
    have hlog : (5 / 4 : ℝ) ≤ Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow, Nat.cast_ofNat]
      linarith only [Real.log_two_gt_d9]
    have h :=
      one_div_le_one_div_of_le (Real.exp_pos _)
        ((Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 4)).mp hlog)
    rw [one_div (Real.exp _), ← Real.exp_neg] at h
    simp only [Nat.cast_zero, add_zero] at hz ⊢
    have hb : 1 - Real.exp (-(5 * (1 / 4 : ℝ))) ≤ 3 / 4 := by
      rw [show (5 : ℝ) * (1 / 4) = 5 / 4 by ring]
      linarith only [h]
    have hs := pow_le_pow_left₀ hz hb 2
    apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans
    apply le_of_eq
    ring
  | succ n =>
    have hs := pow_le_pow_left₀ hz (sub_le_self _ (Real.exp_pos _).le) 2
    have hd : 1 ≤ 4 * (1 / 4 + ((n + 1 : ℕ) : ℝ)) ^ 2 := by
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]
    have ht := div_le_self Real.pi_pos.le hd
    apply (mul_le_mul_of_nonneg_left hs (by positivity)).trans
    rw [one_pow, mul_one]
    linarith only [ht, Real.pi_pos]

/-- At every radius from 287 onward the normalized translated even digamma
correction is strictly smaller than 1/250 in absolute value. -/
theorem triangle_translated_error_bound {r : ℝ} (hr : 287 ≤ r) :
    (2 / 5) *
          |∫ t : ℝ,
              (1 / 2 : ℝ) *
                ((Complex.digamma (1 / 4 + Complex.I * (t / 2))).re -
                  (Complex.digamma (1 / 4)).re) *
                ‖Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)‖ *
                Real.cos ((2 * Real.log r + 5 / 2) * t)| /
        Real.pi <
      1 / 250 := by
  have hp : 0 < r := by linarith only [hr]
  have hl := Real.log_nonneg (show 1 ≤ r by linarith only [hr])
  have he :=
    triangle_translated_series (a := 5 / 4) (b := 1 / 4) (v := 2 * Real.log r + 5 / 2)
      (by norm_num only) (by norm_num only) (by linarith only [hl])
  push_cast at he
  rw [he]
  let A := (9 / 4) * Real.pi * r⁻¹
  have hgeom :=
    (hasSum_geometric_of_lt_one (by norm_num only : (0 : ℝ) ≤ 1 / 10)
          (by norm_num only : (1 / 10 : ℝ) < 1)).mul_left
      A
  have hbound :=
    tsum_of_norm_bounded hgeom (f := fun n : ℕ =>
      -(Real.pi / (4 * (1 / 4 + n) ^ 2)) *
        Real.exp (-(2 * (1 / 4 + n)) * (2 * Real.log r + 5 / 2 - 2 * (5 / 4))) *
        (1 - Real.exp (-(4 * (5 / 4) * (1 / 4 + n)))) ^ 2)
      (by
        intro n
        rw [show 2 * Real.log r + 5 / 2 - 2 * (5 / 4) = 2 * Real.log r by ring,
          show (4 : ℝ) * (5 / 4) = 5 by ring, Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
          abs_of_nonneg (by positivity : 0 ≤ Real.pi / (4 * (1 / 4 + n) ^ 2)),
          abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _), mul_right_comm]
        exact
          (mul_le_mul (shifted_pole_coefficient n) (shifted_pole_decay hr n) (Real.exp_pos _).le
                (by positivity)).trans_eq
            (by
              unfold A; ring))
  rw [Real.norm_eq_abs] at hbound
  apply (div_lt_iff₀ Real.pi_pos).2
  apply (mul_le_mul_of_nonneg_left hbound (by norm_num only : (0 : ℝ) ≤ 2 / 5)).trans_lt
  unfold A
  calc
    _ = Real.pi / r := by ring
    _ < _ := by
      rw [div_lt_iff₀ hp]; nlinarith only [mul_le_mul_of_nonneg_left hr Real.pi_pos.le, Real.pi_pos]

end PseudoPrime.PrimeTestBounds.MillerRabin
