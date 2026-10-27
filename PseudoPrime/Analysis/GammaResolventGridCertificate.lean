/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCompact
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Kernel-checked finite certificate for global Gamma resolvent domination

Rational Taylor and squared-norm checks certify the 8001 grid nodes. Their soundness
connects the finite arithmetic to the actual Gamma norm, curvature and tail proofs.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative x, every finite even Taylor sum is at most cosh x.
The convergent cosh series has nonnegative terms, so omitted terms only increase the value. -/
private theorem cosh_partialSum_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (∑ k ∈ Finset.range n, x ^ (2 * k) / ((2 * k).factorial : ℝ)) ≤ Real.cosh x := by
  rw [Real.cosh_eq_tsum]
  exact
    Summable.sum_le_tsum (Finset.range n)
      (fun k _ ↦ div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _)) (Real.hasSum_cosh x).summable

/-- The degree-32 even Taylor polynomial for cosh, evaluated exactly over
rationals. This lower bound replaces transcendental evaluation in the finite checks. -/
private def coshTaylorQ (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 17, x ^ (2 * k) / ((2 * k).factorial : ℚ)

/-- The rational scaled resolvent value at j/500 minus 1/25000.
A nonnegative radius bounds the scaled Gamma norm when the squared cosh check succeeds. -/
private def gammaResolventNodeRadius (j : ℕ) : ℚ :=
  (1 + ((j : ℚ) / 500) ^ 2) *
      (gammaResolventCoefficients.map
          (fun ab ↦ ab.2 * (ab.1 / (ab.1 ^ 2 + ((j : ℚ) / 500) ^ 2)))).sum -
    1 / 25000

/-- A Boolean check of the radius sign and the squared Gamma comparison
using rational lower and upper bounds for π. Every accepted node is justified analytically. -/
private def gammaResolventNodeCheck (j : ℕ) : Bool :=
  decide
    (0 ≤ gammaResolventNodeRadius j ∧
      (157079633 / 50000000 : ℚ) * (1 + ((j : ℚ) / 500) ^ 2) ^ 2 ≤
        gammaResolventNodeRadius j ^ 2 *
          coshTaylorQ ((314159265 / 100000000 : ℚ) * ((j : ℚ) / 500)))

/-- The rational Taylor polynomial casts to a lower bound for real cosh
at nonnegative rational inputs. Casting commutes with the finite sum, powers and division. -/
private theorem coshTaylorQ_le_cosh {x : ℚ} (hx : 0 ≤ x) :
    (coshTaylorQ x : ℝ) ≤ Real.cosh (x : ℝ) := by
  rw [coshTaylorQ, Rat.cast_sum]
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  exact cosh_partialSum_le (Rat.cast_nonneg.mpr hx) 17

/-- The rational node radius casts exactly to the real scaled resolvent
minus 1/25000. Distribute the casts through the signed finite sum without approximation. -/
private theorem radius_cast (j : ℕ) :
    (gammaResolventNodeRadius j : ℝ) = gammaResolventScaled ((j : ℝ) / 500) - 1 / 25000 := by
  simp only [gammaResolventNodeRadius, gammaResolventScaled, gammaResolventMajorant, Rat.cast_sub,
    Rat.cast_mul, Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_list_sum, List.map_map]
  congr 2
  apply congrArg List.sum
  apply List.map_congr_left
  intro ab _hab
  simp only [Function.comp_apply, Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat]

/-- An accepted rational node check gives scaled gap at least 1/25000.
Use certified π bounds, the nonnegative cosh Taylor lower bound and a squared comparison;
then cancel the positive scaling factor. No external numerical computation is assumed. -/
private theorem gammaResolventNodeCheck_sound (j : ℕ) (h : gammaResolventNodeCheck j = true) :
    (1 / 25000 : ℝ) ≤ gammaResolventScaledGap ((j : ℝ) / 500) := by
  have hq := of_decide_eq_true h
  have hr : 0 ≤ (gammaResolventNodeRadius j : ℝ) := Rat.cast_nonneg.mpr hq.1
  have hn :
    (157079633 / 50000000 : ℝ) * (1 + ((j : ℝ) / 500) ^ 2) ^ 2 ≤
      (gammaResolventNodeRadius j : ℝ) ^ 2 *
        (coshTaylorQ ((314159265 / 100000000 : ℚ) * ((j : ℚ) / 500)) : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).mpr hq.2
    simpa only [Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_one, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat] using hcast
  have ht : 0 ≤ (j : ℝ) / 500 := div_nonneg (Nat.cast_nonneg _) (by norm_num only)
  have hpLo : (314159265 / 100000000 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d20]
  have hpHi : Real.pi ≤ (157079633 / 50000000 : ℝ) := by linarith only [Real.pi_lt_d20]
  have hx : 0 ≤ (314159265 / 100000000 : ℚ) * ((j : ℚ) / 500) :=
    mul_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg _) (by norm_num only))
  have hpoly := coshTaylorQ_le_cosh hx
  have hxReal :
    (((314159265 / 100000000 : ℚ) * ((j : ℚ) / 500) : ℚ) : ℝ) =
      (314159265 / 100000000 : ℝ) * ((j : ℝ) / 500) := by
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  rw [hxReal] at hpoly
  have hc :
    Real.cosh ((314159265 / 100000000 : ℝ) * ((j : ℝ) / 500)) ≤
      Real.cosh (Real.pi * ((j : ℝ) / 500)) :=
    Real.cosh_le_cosh.mpr
      (by
        rw [abs_of_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 314159265 / 100000000) ht),
          abs_of_nonneg (mul_nonneg Real.pi_pos.le ht)]
        exact mul_le_mul_of_nonneg_right hpLo ht)
  have hc' :=
    mul_le_mul_of_nonneg_left (hpoly.trans hc) (sq_nonneg (gammaResolventNodeRadius j : ℝ))
  have hp' := mul_le_mul_of_nonneg_right hpHi (sq_nonneg (1 + ((j : ℝ) / 500) ^ 2))
  have hprod := hp'.trans (hn.trans hc')
  have hpos : 0 < 1 + ((j : ℝ) / 500) ^ 2 :=
    add_pos_of_pos_of_nonneg (by norm_num only) (sq_nonneg _)
  have hratio :
    Real.pi / Real.cosh (Real.pi * ((j : ℝ) / 500)) ≤
      ((gammaResolventNodeRadius j : ℝ) / (1 + ((j : ℝ) / 500) ^ 2)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (Real.cosh_pos _) (pow_pos hpos 2)]
    exact hprod
  have hs := Real.sqrt_le_iff.mpr ⟨div_nonneg hr hpos.le, hratio⟩
  have hm := (le_div_iff₀ hpos).mp hs
  rw [radius_cast, mul_comm] at hm
  change
    (1 + ((j : ℝ) / 500) ^ 2) * gammaHalfLineNorm ((j : ℝ) / 500) ≤
      gammaResolventScaled ((j : ℝ) / 500) - 1 / 25000 at hm
  change
    1 / 25000 ≤
      gammaResolventScaled ((j : ℝ) / 500) -
        (1 + ((j : ℝ) / 500) ^ 2) * gammaHalfLineNorm ((j : ℝ) / 500)
  linarith only [hm]

/-- Evaluate a Boolean predicate on 2^n consecutive natural indices,
starting at start. A balanced recursion keeps evaluation depth logarithmic in the node count. -/
private def balancedGridCheck (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, start => p start
  | n + 1, start => balancedGridCheck p n start && balancedGridCheck p n (start + 2 ^ n)

/-- A successful balanced check certifies every index in its block.
Induction splits the block at 2^n and translates indices into the accepted half. -/
private theorem balancedGridCheck_sound (p : ℕ → Bool) (n start : ℕ)
    (h : balancedGridCheck p n start = true) {j : ℕ} (hj : j < 2 ^ n) : p (start + j) = true := by
  induction n generalizing start j with
  | zero =>
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    simpa only [hj0, Nat.add_zero, balancedGridCheck] using h
  | succ n ih =>
    simp only [balancedGridCheck, Bool.and_eq_true] at h
    by_cases hl : j < 2 ^ n
    · exact ih start h.1 hl
    · have hle : 2 ^ n ≤ j := Nat.le_of_not_gt hl
      have hj' : j - 2 ^ n < 2 ^ n :=
        (Nat.sub_lt_iff_lt_add hle).mpr (by simpa only [Nat.pow_succ, Nat.mul_two] using hj)
      have hr := ih (start + 2 ^ n) h.2 hj'
      rw [Nat.add_assoc, Nat.add_sub_of_le hle] at hr
      exact hr

/-- Apply the node checker exactly on j≤8000; padding leaves are accepted without
additional arithmetic. The balanced block has 8192 leaves and requires only 8001 nodes. -/
private def gammaResolventGridPredicate (j : ℕ) : Bool :=
  if j ≤ 8000 then gammaResolventNodeCheck j else true

/-- Kernel-check nodes 0 through 127 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_0 :
    balancedGridCheck gammaResolventGridPredicate 7 0 = true := by decide +kernel

/-- Kernel-check nodes 128 through 255 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_1 :
    balancedGridCheck gammaResolventGridPredicate 7 128 = true := by decide +kernel

/-- Kernel-check nodes 256 through 383 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_2 :
    balancedGridCheck gammaResolventGridPredicate 7 256 = true := by decide +kernel

/-- Kernel-check nodes 384 through 511 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_3 :
    balancedGridCheck gammaResolventGridPredicate 7 384 = true := by decide +kernel

/-- Kernel-check nodes 512 through 639 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_4 :
    balancedGridCheck gammaResolventGridPredicate 7 512 = true := by decide +kernel

/-- Kernel-check nodes 640 through 767 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_5 :
    balancedGridCheck gammaResolventGridPredicate 7 640 = true := by decide +kernel

/-- Kernel-check nodes 768 through 895 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_6 :
    balancedGridCheck gammaResolventGridPredicate 7 768 = true := by decide +kernel

/-- Kernel-check nodes 896 through 1023 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_7 :
    balancedGridCheck gammaResolventGridPredicate 7 896 = true := by decide +kernel

/-- Kernel-check nodes 1024 through 1151 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_8 :
    balancedGridCheck gammaResolventGridPredicate 7 1024 = true := by decide +kernel

/-- Kernel-check nodes 1152 through 1279 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_9 :
    balancedGridCheck gammaResolventGridPredicate 7 1152 = true := by decide +kernel

/-- Kernel-check nodes 1280 through 1407 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_10 :
    balancedGridCheck gammaResolventGridPredicate 7 1280 = true := by decide +kernel

/-- Kernel-check nodes 1408 through 1535 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_11 :
    balancedGridCheck gammaResolventGridPredicate 7 1408 = true := by decide +kernel

/-- Kernel-check nodes 1536 through 1663 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_12 :
    balancedGridCheck gammaResolventGridPredicate 7 1536 = true := by decide +kernel

/-- Kernel-check nodes 1664 through 1791 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_13 :
    balancedGridCheck gammaResolventGridPredicate 7 1664 = true := by decide +kernel

/-- Kernel-check nodes 1792 through 1919 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_14 :
    balancedGridCheck gammaResolventGridPredicate 7 1792 = true := by decide +kernel

/-- Kernel-check nodes 1920 through 2047 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_15 :
    balancedGridCheck gammaResolventGridPredicate 7 1920 = true := by decide +kernel

/-- Kernel-check nodes 2048 through 2175 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_16 :
    balancedGridCheck gammaResolventGridPredicate 7 2048 = true := by decide +kernel

/-- Kernel-check nodes 2176 through 2303 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_17 :
    balancedGridCheck gammaResolventGridPredicate 7 2176 = true := by decide +kernel

/-- Kernel-check nodes 2304 through 2431 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_18 :
    balancedGridCheck gammaResolventGridPredicate 7 2304 = true := by decide +kernel

/-- Kernel-check nodes 2432 through 2559 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_19 :
    balancedGridCheck gammaResolventGridPredicate 7 2432 = true := by decide +kernel

/-- Kernel-check nodes 2560 through 2687 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_20 :
    balancedGridCheck gammaResolventGridPredicate 7 2560 = true := by decide +kernel

/-- Kernel-check nodes 2688 through 2815 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_21 :
    balancedGridCheck gammaResolventGridPredicate 7 2688 = true := by decide +kernel

/-- Kernel-check nodes 2816 through 2943 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_22 :
    balancedGridCheck gammaResolventGridPredicate 7 2816 = true := by decide +kernel

/-- Kernel-check nodes 2944 through 3071 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_23 :
    balancedGridCheck gammaResolventGridPredicate 7 2944 = true := by decide +kernel

/-- Kernel-check nodes 3072 through 3199 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_24 :
    balancedGridCheck gammaResolventGridPredicate 7 3072 = true := by decide +kernel

/-- Kernel-check nodes 3200 through 3327 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_25 :
    balancedGridCheck gammaResolventGridPredicate 7 3200 = true := by decide +kernel

/-- Kernel-check nodes 3328 through 3455 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_26 :
    balancedGridCheck gammaResolventGridPredicate 7 3328 = true := by decide +kernel

/-- Kernel-check nodes 3456 through 3583 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_27 :
    balancedGridCheck gammaResolventGridPredicate 7 3456 = true := by decide +kernel

/-- Kernel-check nodes 3584 through 3711 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_28 :
    balancedGridCheck gammaResolventGridPredicate 7 3584 = true := by decide +kernel

/-- Kernel-check nodes 3712 through 3839 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_29 :
    balancedGridCheck gammaResolventGridPredicate 7 3712 = true := by decide +kernel

/-- Kernel-check nodes 3840 through 3967 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_30 :
    balancedGridCheck gammaResolventGridPredicate 7 3840 = true := by decide +kernel

/-- Kernel-check nodes 3968 through 4095 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_31 :
    balancedGridCheck gammaResolventGridPredicate 7 3968 = true := by decide +kernel

/-- Kernel-check nodes 4096 through 4223 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_32 :
    balancedGridCheck gammaResolventGridPredicate 7 4096 = true := by decide +kernel

/-- Kernel-check nodes 4224 through 4351 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_33 :
    balancedGridCheck gammaResolventGridPredicate 7 4224 = true := by decide +kernel

/-- Kernel-check nodes 4352 through 4479 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_34 :
    balancedGridCheck gammaResolventGridPredicate 7 4352 = true := by decide +kernel

/-- Kernel-check nodes 4480 through 4607 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_35 :
    balancedGridCheck gammaResolventGridPredicate 7 4480 = true := by decide +kernel

/-- Kernel-check nodes 4608 through 4735 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_36 :
    balancedGridCheck gammaResolventGridPredicate 7 4608 = true := by decide +kernel

/-- Kernel-check nodes 4736 through 4863 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_37 :
    balancedGridCheck gammaResolventGridPredicate 7 4736 = true := by decide +kernel

/-- Kernel-check nodes 4864 through 4991 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_38 :
    balancedGridCheck gammaResolventGridPredicate 7 4864 = true := by decide +kernel

/-- Kernel-check nodes 4992 through 5119 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_39 :
    balancedGridCheck gammaResolventGridPredicate 7 4992 = true := by decide +kernel

/-- Kernel-check nodes 5120 through 5247 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_40 :
    balancedGridCheck gammaResolventGridPredicate 7 5120 = true := by decide +kernel

/-- Kernel-check nodes 5248 through 5375 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_41 :
    balancedGridCheck gammaResolventGridPredicate 7 5248 = true := by decide +kernel

/-- Kernel-check nodes 5376 through 5503 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_42 :
    balancedGridCheck gammaResolventGridPredicate 7 5376 = true := by decide +kernel

/-- Kernel-check nodes 5504 through 5631 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_43 :
    balancedGridCheck gammaResolventGridPredicate 7 5504 = true := by decide +kernel

/-- Kernel-check nodes 5632 through 5759 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_44 :
    balancedGridCheck gammaResolventGridPredicate 7 5632 = true := by decide +kernel

/-- Kernel-check nodes 5760 through 5887 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_45 :
    balancedGridCheck gammaResolventGridPredicate 7 5760 = true := by decide +kernel

/-- Kernel-check nodes 5888 through 6015 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_46 :
    balancedGridCheck gammaResolventGridPredicate 7 5888 = true := by decide +kernel

/-- Kernel-check nodes 6016 through 6143 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_47 :
    balancedGridCheck gammaResolventGridPredicate 7 6016 = true := by decide +kernel

/-- Kernel-check nodes 6144 through 6271 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_48 :
    balancedGridCheck gammaResolventGridPredicate 7 6144 = true := by decide +kernel

/-- Kernel-check nodes 6272 through 6399 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_49 :
    balancedGridCheck gammaResolventGridPredicate 7 6272 = true := by decide +kernel

/-- Kernel-check nodes 6400 through 6527 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_50 :
    balancedGridCheck gammaResolventGridPredicate 7 6400 = true := by decide +kernel

/-- Kernel-check nodes 6528 through 6655 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_51 :
    balancedGridCheck gammaResolventGridPredicate 7 6528 = true := by decide +kernel

/-- Kernel-check nodes 6656 through 6783 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_52 :
    balancedGridCheck gammaResolventGridPredicate 7 6656 = true := by decide +kernel

/-- Kernel-check nodes 6784 through 6911 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_53 :
    balancedGridCheck gammaResolventGridPredicate 7 6784 = true := by decide +kernel

/-- Kernel-check nodes 6912 through 7039 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_54 :
    balancedGridCheck gammaResolventGridPredicate 7 6912 = true := by decide +kernel

/-- Kernel-check nodes 7040 through 7167 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_55 :
    balancedGridCheck gammaResolventGridPredicate 7 7040 = true := by decide +kernel

/-- Kernel-check nodes 7168 through 7295 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_56 :
    balancedGridCheck gammaResolventGridPredicate 7 7168 = true := by decide +kernel

/-- Kernel-check nodes 7296 through 7423 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_57 :
    balancedGridCheck gammaResolventGridPredicate 7 7296 = true := by decide +kernel

/-- Kernel-check nodes 7424 through 7551 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_58 :
    balancedGridCheck gammaResolventGridPredicate 7 7424 = true := by decide +kernel

/-- Kernel-check nodes 7552 through 7679 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_59 :
    balancedGridCheck gammaResolventGridPredicate 7 7552 = true := by decide +kernel

/-- Kernel-check nodes 7680 through 7807 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_60 :
    balancedGridCheck gammaResolventGridPredicate 7 7680 = true := by decide +kernel

/-- Kernel-check nodes 7808 through 7935 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_61 :
    balancedGridCheck gammaResolventGridPredicate 7 7808 = true := by decide +kernel

/-- Kernel-check nodes 7936 through 8000 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_62 :
    balancedGridCheck gammaResolventGridPredicate 7 7936 = true := by decide +kernel

/-- Kernel-check nodes 8064 through 8000 in a balanced block of 128 leaves.
Padding indices above 8000 contribute no obligation. -/
private theorem gammaResolvent_grid_block_63 :
    balancedGridCheck gammaResolventGridPredicate 7 8064 = true := by decide +kernel

/-- All 8001 required nodes pass the checker. Combine the kernel-checked blocks
using only Boolean conjunction, keeping individual numerical reductions bounded. -/
private theorem gammaResolvent_grid_checked :
    balancedGridCheck gammaResolventGridPredicate 13 0 = true := by
  exact
    (Bool.and_eq_true _ _).mpr
      ⟨(Bool.and_eq_true _ _).mpr
          ⟨(Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_0, gammaResolvent_grid_block_1⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_2, gammaResolvent_grid_block_3⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_4, gammaResolvent_grid_block_5⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_6, gammaResolvent_grid_block_7⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_8, gammaResolvent_grid_block_9⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_10, gammaResolvent_grid_block_11⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_12, gammaResolvent_grid_block_13⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_14, gammaResolvent_grid_block_15⟩⟩⟩⟩,
            (Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_16, gammaResolvent_grid_block_17⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_18, gammaResolvent_grid_block_19⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_20, gammaResolvent_grid_block_21⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_22, gammaResolvent_grid_block_23⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_24, gammaResolvent_grid_block_25⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_26, gammaResolvent_grid_block_27⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_28, gammaResolvent_grid_block_29⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_30, gammaResolvent_grid_block_31⟩⟩⟩⟩⟩,
        (Bool.and_eq_true _ _).mpr
          ⟨(Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_32, gammaResolvent_grid_block_33⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_34, gammaResolvent_grid_block_35⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_36, gammaResolvent_grid_block_37⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_38, gammaResolvent_grid_block_39⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_40, gammaResolvent_grid_block_41⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_42, gammaResolvent_grid_block_43⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_44, gammaResolvent_grid_block_45⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_46, gammaResolvent_grid_block_47⟩⟩⟩⟩,
            (Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_48, gammaResolvent_grid_block_49⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_50, gammaResolvent_grid_block_51⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_52, gammaResolvent_grid_block_53⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_54, gammaResolvent_grid_block_55⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_56, gammaResolvent_grid_block_57⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_58, gammaResolvent_grid_block_59⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_60, gammaResolvent_grid_block_61⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨gammaResolvent_grid_block_62, gammaResolvent_grid_block_63⟩⟩⟩⟩⟩⟩

/-- Every node j/500 with j≤8000 has scaled gap at least 1/25000.
Extract its successful Boolean check from the balanced block and apply soundness. -/
theorem gammaResolvent_grid_lower (j : ℕ) (hj : j ≤ 8000) :
    (1 / 25000 : ℝ) ≤ gammaResolventScaledGap ((j : ℝ) / 500) := by
  have hb : j < 2 ^ (13 : ℕ) := Nat.lt_of_le_of_lt hj (by norm_num only : 8000 < 2 ^ (13 : ℕ))
  have h := balancedGridCheck_sound _ 13 0 gammaResolvent_grid_checked hb
  have hc : gammaResolventNodeCheck j = true := by
    simpa only [Nat.zero_add, gammaResolventGridPredicate, ite_eq_left hj] using h
  exact gammaResolventNodeCheck_sound j hc

/-- The fixed signed rational resolvent dominates the Gamma norm at every
real height. All finite node checks, the actual curvature bounds, interpolation, evenness
and the rational-exponential tail have been proved; there is no majorant hypothesis. -/
theorem norm_Gamma_half_add_I_le_gammaResolvent (t : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ ≤ gammaResolventMajorant t := by
  exact norm_Gamma_half_add_I_le_gammaResolvent_of_grid gammaResolvent_grid_lower t

end PseudoPrime.Analysis
