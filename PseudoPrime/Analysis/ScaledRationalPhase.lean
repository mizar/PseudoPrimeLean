/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPhaseTaylor

/-! # Certified range reduction with rounded phase squaring -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a unit complex number z and approximation w at distance at most e.
Claim: the squared values differ by at most e*(2+e).
Proof: factor the square difference and bound the approximate norm by 1+e.
Role: propagate error through range-reduction squaring. -/
theorem norm_square_sub_square_le {z w : ℂ} {e : ℝ} (hz : ‖z‖ = 1) (he : ‖z - w‖ ≤ e) :
    ‖z ^ 2 - w ^ 2‖ ≤ e * (2 + e) := by
  have he0 : 0 ≤ e := (norm_nonneg _).trans he
  have hw := norm_le_norm_sub_add w z
  rw [norm_sub_rev w z, hz] at hw
  have hs := norm_add_le z w
  rw [hz] at hs
  have hf : z ^ 2 - w ^ 2 = (z - w) * (z + w) := by ring
  rw [hf, norm_mul]
  exact mul_le_mul he (by linarith only [hs, hw, he]) (norm_nonneg _) he0

/-- Input: a grid denominator and rational complex pair.
Output: its componentwise square rounded onto the grid.
Role: prevent denominator growth during phase reconstruction. -/
def rationalRoundedSquare (G : ℕ) (w : ℚ × ℚ) : ℚ × ℚ :=
  rationalComplexRound G (rationalComplexMul w w)

/-- Input: a positive grid and approximation to a unit complex value.
Claim: a rounded square has error at most e*(2+e)+2/G.
Proof: combine the square error and the existing rational grid rounding bound.
Role: certify one executable reconstruction step. -/
theorem norm_rounded_square_error {G : ℕ} (hG : 0 < G) {z : ℂ} (hz : ‖z‖ = 1) (w : ℚ × ℚ) {e : ℝ}
    (he : ‖z - rationalComplexCast w‖ ≤ e) :
    ‖z ^ 2 - rationalComplexCast (rationalRoundedSquare G w)‖ ≤ e * (2 + e) + 2 / (G : ℝ) := by
  have ht :=
    norm_sub_le_norm_sub_add_norm_sub (z ^ 2) (rationalComplexCast w ^ 2)
      (rationalComplexCast (rationalRoundedSquare G w))
  have hr := norm_rationalComplexRound_error hG (rationalComplexMul w w)
  rw [rationalComplexCast_mul, ← pow_two] at hr
  rw [norm_sub_rev] at hr
  exact ht.trans (add_le_add (norm_square_sub_square_le hz he) hr)

/-- Input: a grid, initial pair and iteration count. Output: iterated rounded squares.
Definition: retain the initial pair at zero and round each subsequent square.
Role: reconstruct a full phase from a reduced phase without growing denominators. -/
def rationalRoundedSquareIter (G : ℕ) (w : ℚ × ℚ) : ℕ → ℚ × ℚ
  | 0 => w
  | k + 1 => rationalRoundedSquare G (rationalRoundedSquareIter G w k)

/-- Input: a grid denominator G and iteration count k.
Output: (4*3^k-1)/G, a rational majorant for the accumulated error.
Role: replace nonlinear error iteration by an executable closed bound. -/
def roundedSquareBudget (G k : ℕ) : ℚ :=
  (4 * 3 ^ k - 1) / (G : ℚ)

/-- Input: any natural grid denominator and iteration count.
Claim: the totalized rational budget is nonnegative.
Proof: bound 3^k below by one. Role: justify monotone multiplication of error bounds. -/
theorem roundedSquareBudget_nonneg (G k : ℕ) : 0 ≤ (roundedSquareBudget G k : ℝ) := by
  have hp : (1 : ℝ) ≤ 3 ^ k := one_le_pow₀ (by norm_num only : (1 : ℝ) ≤ 3)
  dsimp only [roundedSquareBudget]
  norm_num only [Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_natCast]
  exact div_nonneg (by linarith only [hp]) (Nat.cast_nonneg G)

/-- Input: a grid and count. Claim: the next budget is three times the current one plus 2/G.
Proof: expand the power and use ring arithmetic.
Role: bound each rounded squaring error linearly while the budget is at most one. -/
theorem roundedSquareBudget_succ (G k : ℕ) :
    (roundedSquareBudget G (k + 1) : ℝ) = 3 * (roundedSquareBudget G k : ℝ) + 2 / (G : ℝ) := by
  simp only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_natCast, pow_succ]
  ring

/-- Input: a unit complex value, initial error at most 3/G and intermediate budgets at most one.
Claim: k rounded squares approximate the 2^k-th power within (4*3^k-1)/G.
Proof: induct on the iteration count and dominate e*(2+e) by 3e.
Role: certify executable range-reduction reconstruction. -/
theorem norm_rounded_square_iter_error {G : ℕ} (hG : 0 < G) {z : ℂ} (hz : ‖z‖ = 1) (w : ℚ × ℚ)
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
    have hzpow : ‖z ^ (2 ^ k)‖ = 1 := by rw [norm_pow, hz, one_pow]
    have hs := norm_rounded_square_error hG hzpow (rationalRoundedSquareIter G w k) hi
    have hb := hsmall k (Nat.lt_succ_self k)
    have hb0 := roundedSquareBudget_nonneg G k
    rw [pow_succ, pow_mul, rationalRoundedSquareIter]
    rw [roundedSquareBudget_succ]
    have hm := mul_nonneg hb0 (sub_nonneg.mpr hb)
    nlinarith only [hs, hm]

/-- Input: grid, rational phase v, Taylor length n and squaring count k.
Output: the rounded Taylor sum at v/2^k followed by k rounded squares.
Role: evaluate phase endpoints using a low Taylor degree and bounded grid denominators. -/
def rationalScaledPhase (G : ℕ) (v : ℚ) (n k : ℕ) : ℚ × ℚ :=
  rationalRoundedSquareIter G (rationalComplexRound G (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n)) k

/-- Input: a valid reduced Taylor sum with remainder at most 1/G,
and intermediate budgets at most one.
Claim: the scaled evaluator approximates exp(i*v) within the final rational budget.
Proof: round the initial Taylor value and use the iterated-square theorem and exponential powers.
Role: connect the executable evaluator to the actual exponential. -/
theorem norm_scaled_phase_error {G : ℕ} (hG : 0 < G) (v : ℚ) (n k : ℕ)
    (hv : |((v / (2 : ℚ) ^ k : ℚ) : ℝ)| / (n + 1 : ℕ) ≤ 1 / 2)
    (hrem : |((v / (2 : ℚ) ^ k : ℚ) : ℝ)| ^ n / (n.factorial : ℝ) * 2 ≤ 1 / (G : ℝ))
    (hsmall : ∀ j < k, (roundedSquareBudget G j : ℝ) ≤ 1) :
    ‖Complex.exp (Complex.I * (v : ℂ)) - rationalComplexCast (rationalScaledPhase G v n k)‖ ≤
      (roundedSquareBudget G k : ℝ) := by
  have hr := norm_rationalComplexRound_error hG (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n)
  rw [norm_sub_rev] at hr
  have ht := norm_phaseTaylor_error (v / (2 : ℚ) ^ k) n hv
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub (Complex.exp (Complex.I * ((v / (2 : ℚ) ^ k : ℚ) : ℂ)))
      (rationalComplexCast (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n))
      (rationalComplexCast (rationalComplexRound G (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n)))
  have hi :
    ‖Complex.exp (Complex.I * ((v / (2 : ℚ) ^ k : ℚ) : ℂ)) -
          rationalComplexCast (rationalComplexRound G (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n))‖ ≤
      3 / (G : ℝ) := by
    have he : (3 : ℝ) / G = 1 / G + 2 / G := by ring
    rw [he]
    exact htri.trans (add_le_add (ht.trans hrem) hr)
  have hz : ‖Complex.exp (Complex.I * ((v / (2 : ℚ) ^ k : ℚ) : ℂ))‖ = 1 := by
    rw [← Complex.ofReal_ratCast, Complex.norm_exp_I_mul_ofReal]
  have h :=
    norm_rounded_square_iter_error hG hz
      (rationalComplexRound G (rationalPhaseTaylor (v / (2 : ℚ) ^ k) n)) hi k hsmall
  have hp :
    Complex.exp (Complex.I * (v : ℂ)) =
      Complex.exp (Complex.I * ((v / (2 : ℚ) ^ k : ℚ) : ℂ)) ^ (2 ^ k) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    norm_num only [Nat.cast_pow, Nat.cast_ofNat, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]
    have hn : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero k (by norm_num only)
    calc
      Complex.I * (v : ℂ) = Complex.I * (((v : ℂ) / (2 : ℂ) ^ k) * (2 : ℂ) ^ k) := by
        rw [div_mul_cancel₀ _ hn]
      _ = _ := by ring
  rw [hp]
  exact h

/-- Input: a rational phase with absolute value at most 128.
Claim: length 16 and seven squares on grid 10^12 have error at most 8747/10^12.
Proof: bound the reduced phase by one and certify the finite budgets.
Role: provide uniform numerical parameters for low-frequency endpoint certificates. -/
theorem norm_scaled_phase_grid12_error (v : ℚ) (hv : |(v : ℝ)| ≤ 128) :
    ‖Complex.exp (Complex.I * (v : ℂ)) -
          rationalComplexCast (rationalScaledPhase (10 ^ 12) v 16 7)‖ ≤
      (8747 / 1000000000000 : ℝ) := by
  have hq : |((v / (2 : ℚ) ^ 7 : ℚ) : ℝ)| ≤ 1 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hv]
  have hp := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 7 : ℚ) : ℝ)) hq 16
  have h :=
    norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 12) v 16 7
      (by
        norm_num only; linarith only [hq])
      (by
        norm_num only [Nat.factorial] at hp ⊢; nlinarith only [hp])
      (by
        intro j hj
        interval_cases j <;>
          norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
            Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
  norm_num only [roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_natCast] at h
  exact h

end PseudoPrime.Analysis
