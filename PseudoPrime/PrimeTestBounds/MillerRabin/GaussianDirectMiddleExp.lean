/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import PseudoPrime.Analysis.IntegerIntervalComputed
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import Mathlib.Tactic.NormNum

/-! # Fixed-point exponential grid for the direct Gaussian middle range -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The eight-decimal seed used by the binary exponential enclosures. -/
@[expose]
public def gaussianMidExpSeed : Analysis.IntegerInterval :=
  ⟨101257844, 101257852⟩

/-- A positive Taylor subtotal and geometric tail certify the seed at exponent `1/80`. -/
public theorem gaussian_mid_exp_seed :
    gaussianMidExpSeed.Contains 100000000 (Real.exp (1 / 80)) := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 80) 4
  have hu :=
    Analysis.exp_le_taylor_add_two_next (n := 4) (by norm_num only : (0 : ℝ) ≤ 1 / 80)
      (by norm_num only)
  constructor
  · apply le_trans _ hl
    norm_num only [gaussianMidExpSeed, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_succ, Nat.factorial_zero]
  · refine hu.trans ?_
    norm_num only [gaussianMidExpSeed, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_succ, Nat.factorial_zero]

/-- Consume the lower bits of the exponent while sharing the squared base.
The accumulator and base use the same positive fixed-point scale. -/
@[expose]
public def gaussianMidExpFold (G : ℤ) (n : ℕ) (A B : Analysis.IntegerInterval) :
    Analysis.IntegerInterval :=
  if hn : n = 0 then A
  else
    gaussianMidExpFold G (n / 2) (if n % 2 = 0 then A else Analysis.roundedProduct G A B)
      (Analysis.roundedProduct G B B)
termination_by n
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide)

/-- The binary accumulator encloses `a * b^n` whenever its two inputs
enclose `a` and `b` at the common scale. -/
public theorem gaussian_mid_exp_fold_contains {G : ℤ} (hG : 0 < G) (n : ℕ)
    {A B : Analysis.IntegerInterval} {a b : ℝ} (ha : A.Contains G a) (hb : B.Contains G b) :
    (gaussianMidExpFold G n A B).Contains G (a * b ^ n) := by
  induction n using Nat.strong_induction_on generalizing A B a b with
  | ind n ih =>
    by_cases hn : n = 0
    · rw [gaussianMidExpFold, dite_eq_left hn, hn, pow_zero, mul_one]
      exact ha
    rw [gaussianMidExpFold, dite_eq_right hn]
    have hlt := Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide : 1 < 2)
    have hB := Analysis.roundedProduct_contains hG hb hb
    have hp : (b * b) ^ (n / 2) = b ^ (2 * (n / 2)) := by rw [← pow_two, pow_mul]
    have he := Nat.mod_add_div n 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [ite_eq_left h]
      have hv := ih (n / 2) hlt ha hB
      rw [hp] at hv
      rw [h, zero_add] at he
      rwa [he] at hv
    · rw [ite_eq_right (h.trans_ne (by decide))]
      have hv := ih (n / 2) hlt (Analysis.roundedProduct_contains hG ha hb) hB
      rw [hp, mul_assoc, ← pow_succ'] at hv
      rw [h, Nat.add_comm 1] at he
      rw [he] at hv
      exact hv

/-- Compute the enclosure for the positive exponential at grid index `n`. -/
@[expose]
public def gaussianMidExpGrid (n : ℕ) : Analysis.IntegerInterval :=
  gaussianMidExpFold 100000000 n ⟨100000000, 100000000⟩ gaussianMidExpSeed

/-- The eight-decimal binary calculation encloses the exponential at `n/80`. -/
public theorem gaussian_mid_exp_grid (n : ℕ) :
    (gaussianMidExpGrid n).Contains 100000000 (Real.exp ((n : ℝ) / 80)) := by
  have ho : (Analysis.IntegerInterval.mk 100000000 100000000).Contains 100000000 1 := by
    constructor <;> norm_num only
  have h :=
    gaussian_mid_exp_fold_contains (by decide : (0 : ℤ) < 100000000) n ho gaussian_mid_exp_seed
  simpa only [gaussianMidExpGrid, one_mul, ← Real.exp_natCast_mul, mul_one_div] using h

/-- Compute the outward reciprocal of a positive grid value, multiplied by
the nonnegative normalization integer `k` before rounding. -/
@[expose]
public def gaussianMidScaledInv (G k : ℤ) (I : Analysis.IntegerInterval) :
    Analysis.IntegerInterval :=
  let z := k * G * G
  ⟨z / I.upper, -((-z) / I.lower)⟩

/-- At positive scale and positive input ticks, the normalized reciprocal
encloses the scaled inverse. The normalization prevents rounding tiny exponentials to zero. -/
public theorem gaussian_mid_scaled_inv {G k : ℤ} {I : Analysis.IntegerInterval} {x : ℝ} (hG : 0 < G)
    (hk : 0 ≤ k) (hI : 0 < I.lower) (hx : I.Contains G x) :
    (gaussianMidScaledInv G k I).Contains G ((k : ℝ) / x) := by
  have g : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have a : (0 : ℝ) < I.lower := Int.cast_pos.mpr hI
  have b := a.trans_le ((div_le_div_iff_of_pos_right g).mp (hx.1.trans hx.2))
  have xpos := (div_pos a g).trans_le hx.1
  have hkr : (0 : ℝ) ≤ k := Int.cast_nonneg_iff.mpr hk
  let R := gaussianMidScaledInv G k I
  let z := k * G * G
  have hb : 0 < I.upper := Int.cast_pos.mp b
  have hl : R.lower * I.upper ≤ z := (Analysis.round_corner hb (x := z) le_rfl le_rfl).1
  have hu : z ≤ R.upper * I.lower := (Analysis.round_corner hI (x := z) le_rfl le_rfl).2
  have hrl : (R.lower : ℝ) * I.upper ≤ (k : ℝ) * G * G := by
    simpa only [z, Int.cast_mul] using (Int.cast_le (R := ℝ)).mpr hl
  have hru : (k : ℝ) * G * G ≤ (R.upper : ℝ) * I.lower := by
    simpa only [z, Int.cast_mul] using (Int.cast_le (R := ℝ)).mpr hu
  constructor
  · calc
      (R.lower : ℝ) / G ≤ ((k : ℝ) * G) / I.upper := (div_le_div_iff₀ g b).mpr hrl
      _ = (k : ℝ) / ((I.upper : ℝ) / G) := (div_div_eq_mul_div _ _ _).symm
      _ ≤ (k : ℝ) / x := div_le_div_of_nonneg_left hkr xpos hx.2
  · calc
      (k : ℝ) / x ≤ (k : ℝ) / ((I.lower : ℝ) / G) :=
        div_le_div_of_nonneg_left hkr (div_pos a g) hx.1
      _ = ((k : ℝ) * G) / I.lower := div_div_eq_mul_div _ _ _
      _ ≤ (R.upper : ℝ) / G := (div_le_div_iff₀ a g).mpr hru

/-- A positive grid enclosure also supplies the normalized decaying factor
used with the shared polynomial coefficient rows. -/
public theorem gaussian_mid_exp_decay (n : ℕ) (k : ℤ) (hk : 0 ≤ k)
    (hn : 0 < (gaussianMidExpGrid n).lower) :
    (gaussianMidScaledInv 100000000 k (gaussianMidExpGrid n)).Contains 100000000
      ((k : ℝ) * Real.exp (-((n : ℝ) / 80))) := by
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact gaussian_mid_scaled_inv (by decide) hk hn (gaussian_mid_exp_grid n)

end PseudoPrime.PrimeTestBounds.MillerRabin
