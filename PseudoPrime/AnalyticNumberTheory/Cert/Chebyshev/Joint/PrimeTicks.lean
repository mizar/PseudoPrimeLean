/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PrimeLog

/-! # Soundness of binary fixed-point logarithm ticks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The upward-rounded natural quotient times the divisor covers the numerator. -/
private theorem ceil_covers {a d : ℕ} (hd : 0 < d) : (a : ℝ) ≤ (((a + d - 1) / d : ℕ) : ℝ) * d := by
  have h := Nat.lt_mul_div_succ (a + d - 1) hd
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm d ((a + d - 1) / d)] at h
  have h' := Nat.sub_add_cancel (show 1 ≤ a + d from hd.trans_le (Nat.le_add_left d a))
  exact_mod_cast (show a ≤ (a + d - 1) / d * d by linarith only [h, h'])

/-- Binary exponent reduction gives a mantissa index from 32 through 63. -/
private theorem grid_range {p : ℕ} (hp : p ≠ 0) :
    32 ≤ 32 * p / 2 ^ p.log2 ∧ 32 * p / 2 ^ p.log2 < 64 := by
  have h := (Nat.log2_eq_iff hp).mp (rfl : p.log2 = p.log2)
  have hq : 0 < 2 ^ p.log2 := Nat.two_pow_pos _
  constructor
  · exact (Nat.le_div_iff_mul_le hq).2 (Nat.mul_le_mul_left 32 h.1)
  · apply (Nat.div_lt_iff_lt_mul hq).2
    have hu := h.2
    rw [pow_succ] at hu
    linarith only [hu]

/-- Express the input as the product of a binary power, grid value and residual. -/
private theorem binary_product {p k j r d : ℕ} (hj : 32 ≤ j) (hd : 0 < d) (hm : d = j * 2 ^ k)
    (hp : d + r = 32 * p) :
    (p : ℝ) = 2 ^ k * ((32 + ((j - 32 : ℕ) : ℝ)) / 32) * (1 + (r : ℝ) / d) := by
  have hp' : (d : ℝ) + r = 32 * p := by exact_mod_cast hp
  have hm' : (d : ℝ) = (j : ℝ) * 2 ^ k := by exact_mod_cast hm
  have hz := mul_div_cancel₀ (r : ℝ) (Nat.cast_ne_zero.mpr hd.ne')
  rw [Nat.cast_sub hj, Nat.cast_ofNat]
  linear_combination (-hp' + (1 + (r : ℝ) / d) * hm' - hz) / 32

/-- Integer division of the quadratic residual rounds its lower bound downwards. -/
private theorem lower_ticks {s r d : ℕ} (hd : 0 < d) (hr : r ≤ 2 * d) :
    ((s * r * (2 * d - r) / (2 * d * d) : ℕ) : ℝ) ≤
      s * (((r : ℝ) / d) * (2 - (r : ℝ) / d) / 2) := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hn := Nat.div_mul_le_self (s * r * (2 * d - r)) (2 * d * d)
  have h :
    ((s * r * (2 * d - r) / (2 * d * d) : ℕ) : ℝ) * (2 * d * d) ≤ s * (r : ℝ) * (2 * d - r) := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hn
    simpa only [Nat.cast_mul, Nat.cast_sub hr, Nat.cast_ofNat] using hh
  calc
    _ ≤ (s * (r : ℝ) * (2 * d - r)) / (2 * d * d) :=
      (le_div_iff₀ (mul_pos (mul_pos (by norm_num only) hd') hd')).2 h
    _ = _ := by
      apply (div_eq_iff (mul_pos (mul_pos (by norm_num only) hd') hd').ne').2
      have hz := mul_div_cancel₀ (r : ℝ) hd'.ne'
      linear_combination -(s * (2 * (d : ℝ) - r - d * ((r : ℝ) / d))) * hz

/-- Integer ceiling division rounds the linear residual upwards. -/
private theorem upper_ticks {s r d : ℕ} (hd : 0 < d) :
    s * ((r : ℝ) / d) ≤ (((s * r + d - 1) / d : ℕ) : ℝ) := by
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hd)).2
  simpa only [Nat.cast_mul] using ceil_covers (a := s * r) hd

/-- Multiplying the grid decomposition by the positive scale clears both grid denominators. -/
private theorem clear_ticks (k t g z : ℝ) :
    scale * (k * (t / scale) + g / scale + z) = k * t + g + scale * z := by
  have hs : (scale : ℝ) ≠ 0 := by norm_num only [scale, Nat.cast_pow, Nat.cast_ofNat]
  linear_combination k * mul_div_cancel₀ t hs + mul_div_cancel₀ g hs

/-- For positive input the exact runtime ticks enclose its scaled real logarithm.
The binary decomposition selects a certified grid row and the integer quotients
round the two residual estimates outwards. -/
theorem primeTicks_sound {p : ℕ} (hp : p ≠ 0) :
    ((primeTicks gridTicks (gridTicks 32) p).1 : ℝ) ≤ scale * Real.log p ∧
      scale * Real.log p ≤ ((primeTicks gridTicks (gridTicks 32) p).2 : ℝ) := by
  let k := p.log2
  let q := 2 ^ k
  let j := 32 * p / q
  let r := 32 * p % q
  let d := j * q
  have hq : 0 < q := Nat.two_pow_pos _
  obtain ⟨hj, hu⟩ := grid_range hp
  have hj' : 32 ≤ j := hj
  have hd : 0 < d := Nat.mul_pos (Nat.zero_lt_of_lt hj') hq
  have hidx : j - 32 < 32 := by
    have h := Nat.sub_add_cancel hj'
    change j < 64 at hu
    linarith only [h, hu]
  have hr : r < q := Nat.mod_lt _ hq
  have hr' : r ≤ 2 * d := by
    have h : q ≤ d := Nat.le_mul_of_pos_left q (Nat.zero_lt_of_lt hj')
    linarith only [hr, h]
  have hp' : d + r = 32 * p := by simpa only [d, Nat.mul_comm j q] using Nat.div_add_mod (32 * p) q
  have hg :=
    grid_decomp hidx (div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg d))
      (binary_product (k := k) hj' hd rfl hp')
  have hs := Nat.cast_nonneg (α := ℝ) scale
  have hlo := mul_le_mul_of_nonneg_left hg.1 hs
  have hhi := mul_le_mul_of_nonneg_left hg.2 hs
  rw [clear_ticks] at hlo hhi
  change
    ((_ + k * _ + scale * r * (2 * d - r) / (2 * d * d) : ℕ) : ℝ) ≤ _ ∧
      _ ≤ ((_ + k * _ + (scale * r + d - 1) / d : ℕ) : ℝ)
  push_cast only [Nat.cast_add, Nat.cast_mul]
  constructor
  · linarith only [hlo, lower_ticks (s := scale) hd hr']
  · linarith only [hhi, upper_ticks (s := scale) (r := r) hd]

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
