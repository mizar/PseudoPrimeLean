/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ScaledRationalPhase

/-! # Rounded squaring for contractive exponential approximations -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- If the exact complex number has norm at most one and its approximation
has error at most `e`, their squares differ by at most `e * (2 + e)`. -/
theorem norm_square_sub_square_le_one {z w : ℂ} {e : ℝ} (hz : ‖z‖ ≤ 1) (he : ‖z - w‖ ≤ e) :
    ‖z ^ 2 - w ^ 2‖ ≤ e * (2 + e) := by
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have hw := norm_le_norm_sub_add w z
  rw [norm_sub_rev w z] at hw
  have hs := norm_add_le z w
  have hf : z ^ 2 - w ^ 2 = (z - w) * (z + w) := by ring
  rw [hf, norm_mul]
  exact mul_le_mul he (by linarith only [hs, hw, he, hz]) (norm_nonneg _) he0

/-- One rounded square of a rational approximation to a complex value of
norm at most one adds at most `2/G` to the square-error budget. -/
theorem norm_rounded_square_error_le_one {G : ℕ} (hG : 0 < G) {z : ℂ} (hz : ‖z‖ ≤ 1) (w : ℚ × ℚ)
    {e : ℝ} (he : ‖z - rationalComplexCast w‖ ≤ e) :
    ‖z ^ 2 - rationalComplexCast (rationalRoundedSquare G w)‖ ≤ e * (2 + e) + 2 / (G : ℝ) := by
  have ht :=
    norm_sub_le_norm_sub_add_norm_sub (z ^ 2) (rationalComplexCast w ^ 2)
      (rationalComplexCast (rationalRoundedSquare G w))
  have hr := norm_rationalComplexRound_error hG (rationalComplexMul w w)
  rw [rationalComplexCast_mul, ← pow_two, norm_sub_rev] at hr
  exact ht.trans (add_le_add (norm_square_sub_square_le_one hz he) hr)

/-- Repeated rounded squaring approximates the power of any complex value
of norm at most one. The existing budget controls every intermediate error. -/
theorem norm_rounded_square_iter_le_one {G : ℕ} (hG : 0 < G) {z : ℂ} (hz : ‖z‖ ≤ 1) (w : ℚ × ℚ)
    (hinit : ‖z - rationalComplexCast w‖ ≤ 3 / (G : ℝ)) (k : ℕ)
    (hsmall : ∀ j < k, (roundedSquareBudget G j : ℝ) ≤ 1) :
    ‖z ^ (2 ^ k) - rationalComplexCast (rationalRoundedSquareIter G w k)‖ ≤
      (roundedSquareBudget G k : ℝ) := by
  induction k with
  | zero =>
    simpa only [pow_zero, pow_one, rationalRoundedSquareIter, roundedSquareBudget, Rat.cast_div,
      Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_one,
      mul_one, show (4 : ℝ) - 1 = 3 by norm_num only] using hinit
  | succ k ih =>
    have hi := ih (fun j hj ↦ hsmall j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    have hzpow : ‖z ^ (2 ^ k)‖ ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hz
    have hs := norm_rounded_square_error_le_one hG hzpow (rationalRoundedSquareIter G w k) hi
    have hb := hsmall k (Nat.lt_succ_self k)
    have hb0 := roundedSquareBudget_nonneg G k
    rw [pow_succ, pow_mul, rationalRoundedSquareIter, roundedSquareBudget_succ]
    have hm := mul_nonneg hb0 (sub_nonneg.mpr hb)
    nlinarith only [hs, hm]

/-- A rational Taylor polynomial for a real exponential, stored as a
complex component pair with zero imaginary part. -/
def rationalRealExpTaylor (v : ℚ) (n : ℕ) : ℚ × ℚ :=
  (∑ j ∈ Finset.range n, v ^ j / (j.factorial : ℚ), 0)

/-- Casting the rational real Taylor polynomial gives the corresponding
complex Taylor sum. This connects executable arithmetic to the remainder. -/
theorem rational_real_exp_taylor_cast (v : ℚ) (n : ℕ) :
    rationalComplexCast (rationalRealExpTaylor v n) =
      ∑ j ∈ Finset.range n, (v : ℂ) ^ j / (j.factorial : ℂ) := by
  have h :
    rationalComplexCast (rationalRealExpTaylor v n) =
      ((∑ j ∈ Finset.range n, v ^ j / (j.factorial : ℚ) : ℚ) : ℂ) := by
    apply Complex.ext
    · simp only [rationalComplexCast, rationalRealExpTaylor, Complex.ratCast_re]
    · simp only [rationalComplexCast, rationalRealExpTaylor, Rat.cast_zero, Complex.ratCast_im]
  rw [h]
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]

/-- Range reduction for a rational real exponential: approximate the
scaled argument by a Taylor polynomial and reconstruct by rounded squares. -/
def rationalScaledRealExp (G : ℕ) (v : ℚ) (n k : ℕ) : ℚ × ℚ :=
  rationalRoundedSquareIter G (rationalComplexRound G (rationalRealExpTaylor (v / (2 : ℚ) ^ k) n)) k

/-- For a nonpositive rational exponent, a Taylor remainder bound and the
rounded-square budgets certify the range-reduced real exponential value. -/
theorem norm_scaled_real_exp_error {G : ℕ} (hG : 0 < G) (v : ℚ) (hv0 : v ≤ 0) (n k : ℕ)
    (hv : |((v / (2 : ℚ) ^ k : ℚ) : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hrem : |((v / (2 : ℚ) ^ k : ℚ) : ℝ)| ^ n / (n.factorial : ℝ) * 2 ≤ 1 / (G : ℝ))
    (hsmall : ∀ j < k, (roundedSquareBudget G j : ℝ) ≤ 1) :
    ‖Complex.exp (v : ℂ) - rationalComplexCast (rationalScaledRealExp G v n k)‖ ≤
      (roundedSquareBudget G k : ℝ) := by
  let u : ℚ := v / (2 : ℚ) ^ k
  have hn : ‖(u : ℂ)‖ = |(u : ℝ)| := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have ht :=
    Complex.exp_bound' (n := n) (x := (u : ℂ))
      (by
        rw [hn]; exact hv)
  rw [hn, ← rational_real_exp_taylor_cast] at ht
  have hr := norm_rationalComplexRound_error hG (rationalRealExpTaylor u n)
  rw [norm_sub_rev] at hr
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (u : ℂ))
      (rationalComplexCast (rationalRealExpTaylor u n))
      (rationalComplexCast (rationalComplexRound G (rationalRealExpTaylor u n)))
  have hi :
    ‖Complex.exp (u : ℂ) -
          rationalComplexCast (rationalComplexRound G (rationalRealExpTaylor u n))‖ ≤
      3 / (G : ℝ) := by
    have he : (3 : ℝ) / G = 1 / G + 2 / G := by ring
    rw [he]
    exact htri.trans (add_le_add (ht.trans hrem) hr)
  have hu0 : (u : ℝ) ≤ 0 := by
    dsimp only [u]
    have hvR : (v : ℝ) ≤ 0 := by exact_mod_cast hv0
    simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      div_nonpos_of_nonpos_of_nonneg hvR (pow_nonneg (by norm_num only : (0 : ℝ) ≤ 2) k)
  have hz : ‖Complex.exp (u : ℂ)‖ ≤ 1 := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_exp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr hu0
  have h :=
    norm_rounded_square_iter_le_one hG hz (rationalComplexRound G (rationalRealExpTaylor u n)) hi k
      hsmall
  have hp : Complex.exp (v : ℂ) = Complex.exp (u : ℂ) ^ (2 ^ k) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    dsimp only [u]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    have hne : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num only)
    rw [mul_div_cancel₀ _ hne]
  rw [hp]
  exact h

end PseudoPrime.Analysis
