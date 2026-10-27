/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetPowerBounds

/-! # Uniform height-to-level ratios for the original high-zero tail -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- At integer cutoff at least three, a level at most the square root of `H+1`
has its two tail denominator ratios bounded by `2/sqrt(H+1)` and `1/sqrt(H+1)`.
Cross-multiply positive denominators and use the square-root identity. This keeps
the family high-tail cost small while the modulus grows with the height. -/
theorem height_level_ratios_le_inverse_sqrt {H : ℕ} (hH : 3 ≤ H) {q : ℝ}
    (hq : q ≤ Real.sqrt ((H + 1 : ℕ) : ℝ)) :
    q / ((H - 1 : ℕ) : ℝ) ≤ 2 / Real.sqrt ((H + 1 : ℕ) : ℝ) ∧
      q / ((H : ℝ) + 3) ≤ 1 / Real.sqrt ((H + 1 : ℕ) : ℝ) := by
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hRpos : 0 < ((H + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hHr]
  have hsqrt : 0 < Real.sqrt ((H + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr hRpos
  have he : ((H - 1 : ℕ) : ℝ) = (H : ℝ) - 1 := by
    rw [Nat.cast_sub ((by norm_num only : 1 ≤ 3).trans hH), Nat.cast_one]
  have hd1 : 0 < ((H - 1 : ℕ) : ℝ) := by
    rw [he]; linarith only [hHr]
  have hd2 : 0 < (H : ℝ) + 3 := by linarith only [hHr]
  have hmul := mul_le_mul_of_nonneg_right hq hsqrt.le
  have hsq := Real.sq_sqrt hRpos.le
  have hprod : q * Real.sqrt ((H + 1 : ℕ) : ℝ) ≤ (H : ℝ) + 1 := by
    have hp : q * Real.sqrt ((H + 1 : ℕ) : ℝ) ≤ ((H + 1 : ℕ) : ℝ) := by nlinarith only [hmul, hsq]
    exact hp.trans_eq (by rw [Nat.cast_add, Nat.cast_one])
  constructor
  · apply (div_le_div_iff₀ hd1 hsqrt).mpr
    linarith only [hprod, he, hHr]
  · apply (div_le_div_iff₀ hd2 hsqrt).mpr
    linarith only [hprod]

/-- For positive level at most both `H+1` and its square root, cutoff at least
three, and nonnegative scale and tail constant, the level times the original high
zero-tail bound is at most the displayed logarithmic inverse-square-root bound.
Compare both logarithmic numerators with one common height logarithm and apply
the two ratio estimates. This is the height-only contribution to uniform error absorption. -/
theorem weighted_original_high_tail_le {q H : ℕ} {x T : ℝ} (hq : 1 ≤ q) (hH : 3 ≤ H)
    (hqr : q ≤ H + 1) (hsqrt : (q : ℝ) ≤ Real.sqrt ((H + 1 : ℕ) : ℝ)) (hx : 0 ≤ x) (hT : 0 ≤ T) :
    (q : ℝ) *
        (24 * x * T * Real.log q / ((H - 1 : ℕ) : ℝ) +
          192 * x * T * (Real.log ((H + 3 : ℕ) : ℝ) + 2) / (H + 3)) ≤
      240 * x * T * (Real.log 2 + Real.log ((H + 1 : ℕ) : ℝ) + 2) /
        Real.sqrt ((H + 1 : ℕ) : ℝ) := by
  let M := Real.log 2 + Real.log ((H + 1 : ℕ) : ℝ) + 2
  have hHr : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hRpos : 0 < ((H + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith only [hHr]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hlogR : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le H))
  have hM : 0 ≤ M := by
    dsimp only [M]; linarith only [hlog2, hlogR]
  have hqlogR :=
    Real.log_le_log (by exact_mod_cast (Nat.zero_lt_of_lt hq) : (0 : ℝ) < q) (Nat.cast_le.mpr hqr)
  have hqlog : Real.log q ≤ M := by
    dsimp only [M]; linarith only [hqlogR, hlog2]
  have harg : ((H + 3 : ℕ) : ℝ) ≤ 2 * ((H + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    linarith only [hHr]
  have hheight :=
    Real.log_le_log
      (by
        norm_num only [Nat.cast_add, Nat.cast_ofNat]
        linarith only [hHr] : 0 < ((H + 3 : ℕ) : ℝ))
      harg
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) hRpos.ne'] at hheight
  have hheightM : Real.log ((H + 3 : ℕ) : ℝ) + 2 ≤ M := by
    dsimp only [M]
    linarith only [hheight]
  have hr := height_level_ratios_le_inverse_sqrt hH hsqrt
  have h1 :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hqlog hr.1 (div_nonneg (Nat.cast_nonneg q) (Nat.cast_nonneg (H - 1))) hM)
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 24) hx) hT)
  have h2 :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul hheightM hr.2
        (div_nonneg (Nat.cast_nonneg q) (by linarith only [hHr] : 0 ≤ (H : ℝ) + 3)) hM)
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 192) hx) hT)
  change _ ≤ 240 * x * T * M / Real.sqrt ((H + 1 : ℕ) : ℝ)
  convert add_le_add h1 h2 using 1 <;> ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
