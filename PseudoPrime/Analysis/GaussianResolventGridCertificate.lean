/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianResolventNodeBounds

/-! # Kernel-checked global Gaussian resolvent domination

Fixed-point cosh and exponential lower bounds certify every one of the 16001 nodes.
Actual derivatives, interpolation, evenness, and the rational tail extend the result globally.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Evaluate a Boolean predicate on 2^n consecutive natural indices,
starting at start. A balanced recursion keeps evaluation depth logarithmic in the node count. -/
private def gaussianBalancedGridCheck (p : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, start => p start
  | n + 1, start =>
    gaussianBalancedGridCheck p n start && gaussianBalancedGridCheck p n (start + 2 ^ n)

/-- A successful balanced check certifies every index in its block.
Induction splits the block at 2^n and translates indices into the accepted half. -/
private theorem gaussianBalancedGridCheck_sound (p : ℕ → Bool) (n start : ℕ)
    (h : gaussianBalancedGridCheck p n start = true) {j : ℕ} (hj : j < 2 ^ n) :
    p (start + j) = true := by
  induction n generalizing start j with
  | zero =>
    have hj0 : j = 0 := Nat.lt_one_iff.mp hj
    simpa only [hj0, Nat.add_zero, gaussianBalancedGridCheck] using h
  | succ n ih =>
    simp only [gaussianBalancedGridCheck, Bool.and_eq_true] at h
    by_cases hl : j < 2 ^ n
    · exact ih start h.1 hl
    · have hle : 2 ^ n ≤ j := Nat.le_of_not_gt hl
      have hj' : j - 2 ^ n < 2 ^ n :=
        (Nat.sub_lt_iff_lt_add hle).mpr (by simpa only [Nat.pow_succ, Nat.mul_two] using hj)
      have hr := ih (start + 2 ^ n) h.2 hj'
      rw [Nat.add_assoc, Nat.add_sub_of_le hle] at hr
      exact hr

/-- Accept the required indices j≤16000 and pad the balanced tree with true.
The padding avoids adding arithmetic obligations beyond the certified interval. -/
private def gaussianResolventGridPredicate (j : ℕ) : Bool :=
  if j ≤ 16000 then gaussianResolventNodeCheck j else true

/-- Kernel-check the block starting at 0 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_0 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 0 = true := by decide +kernel

/-- Kernel-check the block starting at 128 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_1 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 128 = true := by decide +kernel

/-- Kernel-check the block starting at 256 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_2 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 256 = true := by decide +kernel

/-- Kernel-check the block starting at 384 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_3 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 384 = true := by decide +kernel

/-- Kernel-check the block starting at 512 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_4 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 512 = true := by decide +kernel

/-- Kernel-check the block starting at 640 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_5 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 640 = true := by decide +kernel

/-- Kernel-check the block starting at 768 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_6 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 768 = true := by decide +kernel

/-- Kernel-check the block starting at 896 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_7 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 896 = true := by decide +kernel

/-- Kernel-check the block starting at 1024 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_8 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1024 = true := by decide +kernel

/-- Kernel-check the block starting at 1152 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_9 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1152 = true := by decide +kernel

/-- Kernel-check the block starting at 1280 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_10 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1280 = true := by decide +kernel

/-- Kernel-check the block starting at 1408 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_11 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1408 = true := by decide +kernel

/-- Kernel-check the block starting at 1536 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_12 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1536 = true := by decide +kernel

/-- Kernel-check the block starting at 1664 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_13 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1664 = true := by decide +kernel

/-- Kernel-check the block starting at 1792 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_14 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1792 = true := by decide +kernel

/-- Kernel-check the block starting at 1920 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_15 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 1920 = true := by decide +kernel

/-- Kernel-check the block starting at 2048 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_16 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2048 = true := by decide +kernel

/-- Kernel-check the block starting at 2176 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_17 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2176 = true := by decide +kernel

/-- Kernel-check the block starting at 2304 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_18 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2304 = true := by decide +kernel

/-- Kernel-check the block starting at 2432 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_19 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2432 = true := by decide +kernel

/-- Kernel-check the block starting at 2560 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_20 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2560 = true := by decide +kernel

/-- Kernel-check the block starting at 2688 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_21 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2688 = true := by decide +kernel

/-- Kernel-check the block starting at 2816 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_22 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2816 = true := by decide +kernel

/-- Kernel-check the block starting at 2944 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_23 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 2944 = true := by decide +kernel

/-- Kernel-check the block starting at 3072 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_24 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3072 = true := by decide +kernel

/-- Kernel-check the block starting at 3200 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_25 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3200 = true := by decide +kernel

/-- Kernel-check the block starting at 3328 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_26 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3328 = true := by decide +kernel

/-- Kernel-check the block starting at 3456 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_27 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3456 = true := by decide +kernel

/-- Kernel-check the block starting at 3584 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_28 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3584 = true := by decide +kernel

/-- Kernel-check the block starting at 3712 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_29 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3712 = true := by decide +kernel

/-- Kernel-check the block starting at 3840 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_30 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3840 = true := by decide +kernel

/-- Kernel-check the block starting at 3968 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_31 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 3968 = true := by decide +kernel

/-- Kernel-check the block starting at 4096 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_32 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4096 = true := by decide +kernel

/-- Kernel-check the block starting at 4224 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_33 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4224 = true := by decide +kernel

/-- Kernel-check the block starting at 4352 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_34 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4352 = true := by decide +kernel

/-- Kernel-check the block starting at 4480 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_35 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4480 = true := by decide +kernel

/-- Kernel-check the block starting at 4608 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_36 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4608 = true := by decide +kernel

/-- Kernel-check the block starting at 4736 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_37 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4736 = true := by decide +kernel

/-- Kernel-check the block starting at 4864 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_38 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4864 = true := by decide +kernel

/-- Kernel-check the block starting at 4992 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_39 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 4992 = true := by decide +kernel

/-- Kernel-check the block starting at 5120 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_40 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5120 = true := by decide +kernel

/-- Kernel-check the block starting at 5248 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_41 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5248 = true := by decide +kernel

/-- Kernel-check the block starting at 5376 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_42 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5376 = true := by decide +kernel

/-- Kernel-check the block starting at 5504 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_43 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5504 = true := by decide +kernel

/-- Kernel-check the block starting at 5632 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_44 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5632 = true := by decide +kernel

/-- Kernel-check the block starting at 5760 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_45 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5760 = true := by decide +kernel

/-- Kernel-check the block starting at 5888 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_46 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 5888 = true := by decide +kernel

/-- Kernel-check the block starting at 6016 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_47 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6016 = true := by decide +kernel

/-- Kernel-check the block starting at 6144 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_48 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6144 = true := by decide +kernel

/-- Kernel-check the block starting at 6272 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_49 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6272 = true := by decide +kernel

/-- Kernel-check the block starting at 6400 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_50 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6400 = true := by decide +kernel

/-- Kernel-check the block starting at 6528 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_51 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6528 = true := by decide +kernel

/-- Kernel-check the block starting at 6656 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_52 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6656 = true := by decide +kernel

/-- Kernel-check the block starting at 6784 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_53 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6784 = true := by decide +kernel

/-- Kernel-check the block starting at 6912 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_54 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 6912 = true := by decide +kernel

/-- Kernel-check the block starting at 7040 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_55 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7040 = true := by decide +kernel

/-- Kernel-check the block starting at 7168 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_56 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7168 = true := by decide +kernel

/-- Kernel-check the block starting at 7296 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_57 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7296 = true := by decide +kernel

/-- Kernel-check the block starting at 7424 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_58 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7424 = true := by decide +kernel

/-- Kernel-check the block starting at 7552 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_59 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7552 = true := by decide +kernel

/-- Kernel-check the block starting at 7680 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_60 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7680 = true := by decide +kernel

/-- Kernel-check the block starting at 7808 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_61 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7808 = true := by decide +kernel

/-- Kernel-check the block starting at 7936 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_62 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 7936 = true := by decide +kernel

/-- Kernel-check the block starting at 8064 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_63 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8064 = true := by decide +kernel

/-- Kernel-check the block starting at 8192 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_64 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8192 = true := by decide +kernel

/-- Kernel-check the block starting at 8320 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_65 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8320 = true := by decide +kernel

/-- Kernel-check the block starting at 8448 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_66 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8448 = true := by decide +kernel

/-- Kernel-check the block starting at 8576 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_67 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8576 = true := by decide +kernel

/-- Kernel-check the block starting at 8704 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_68 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8704 = true := by decide +kernel

/-- Kernel-check the block starting at 8832 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_69 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8832 = true := by decide +kernel

/-- Kernel-check the block starting at 8960 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_70 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 8960 = true := by decide +kernel

/-- Kernel-check the block starting at 9088 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_71 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9088 = true := by decide +kernel

/-- Kernel-check the block starting at 9216 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_72 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9216 = true := by decide +kernel

/-- Kernel-check the block starting at 9344 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_73 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9344 = true := by decide +kernel

/-- Kernel-check the block starting at 9472 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_74 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9472 = true := by decide +kernel

/-- Kernel-check the block starting at 9600 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_75 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9600 = true := by decide +kernel

/-- Kernel-check the block starting at 9728 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_76 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9728 = true := by decide +kernel

/-- Kernel-check the block starting at 9856 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_77 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9856 = true := by decide +kernel

/-- Kernel-check the block starting at 9984 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_78 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 9984 = true := by decide +kernel

/-- Kernel-check the block starting at 10112 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_79 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10112 = true := by decide +kernel

/-- Kernel-check the block starting at 10240 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_80 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10240 = true := by decide +kernel

/-- Kernel-check the block starting at 10368 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_81 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10368 = true := by decide +kernel

/-- Kernel-check the block starting at 10496 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_82 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10496 = true := by decide +kernel

/-- Kernel-check the block starting at 10624 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_83 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10624 = true := by decide +kernel

/-- Kernel-check the block starting at 10752 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_84 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10752 = true := by decide +kernel

/-- Kernel-check the block starting at 10880 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_85 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 10880 = true := by decide +kernel

/-- Kernel-check the block starting at 11008 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_86 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11008 = true := by decide +kernel

/-- Kernel-check the block starting at 11136 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_87 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11136 = true := by decide +kernel

/-- Kernel-check the block starting at 11264 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_88 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11264 = true := by decide +kernel

/-- Kernel-check the block starting at 11392 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_89 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11392 = true := by decide +kernel

/-- Kernel-check the block starting at 11520 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_90 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11520 = true := by decide +kernel

/-- Kernel-check the block starting at 11648 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_91 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11648 = true := by decide +kernel

/-- Kernel-check the block starting at 11776 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_92 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11776 = true := by decide +kernel

/-- Kernel-check the block starting at 11904 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_93 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 11904 = true := by decide +kernel

/-- Kernel-check the block starting at 12032 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_94 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12032 = true := by decide +kernel

/-- Kernel-check the block starting at 12160 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_95 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12160 = true := by decide +kernel

/-- Kernel-check the block starting at 12288 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_96 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12288 = true := by decide +kernel

/-- Kernel-check the block starting at 12416 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_97 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12416 = true := by decide +kernel

/-- Kernel-check the block starting at 12544 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_98 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12544 = true := by decide +kernel

/-- Kernel-check the block starting at 12672 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_99 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12672 = true := by decide +kernel

/-- Kernel-check the block starting at 12800 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_100 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12800 = true := by decide +kernel

/-- Kernel-check the block starting at 12928 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_101 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 12928 = true := by decide +kernel

/-- Kernel-check the block starting at 13056 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_102 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13056 = true := by decide +kernel

/-- Kernel-check the block starting at 13184 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_103 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13184 = true := by decide +kernel

/-- Kernel-check the block starting at 13312 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_104 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13312 = true := by decide +kernel

/-- Kernel-check the block starting at 13440 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_105 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13440 = true := by decide +kernel

/-- Kernel-check the block starting at 13568 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_106 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13568 = true := by decide +kernel

/-- Kernel-check the block starting at 13696 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_107 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13696 = true := by decide +kernel

/-- Kernel-check the block starting at 13824 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_108 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13824 = true := by decide +kernel

/-- Kernel-check the block starting at 13952 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_109 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 13952 = true := by decide +kernel

/-- Kernel-check the block starting at 14080 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_110 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14080 = true := by decide +kernel

/-- Kernel-check the block starting at 14208 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_111 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14208 = true := by decide +kernel

/-- Kernel-check the block starting at 14336 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_112 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14336 = true := by decide +kernel

/-- Kernel-check the block starting at 14464 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_113 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14464 = true := by decide +kernel

/-- Kernel-check the block starting at 14592 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_114 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14592 = true := by decide +kernel

/-- Kernel-check the block starting at 14720 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_115 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14720 = true := by decide +kernel

/-- Kernel-check the block starting at 14848 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_116 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14848 = true := by decide +kernel

/-- Kernel-check the block starting at 14976 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_117 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 14976 = true := by decide +kernel

/-- Kernel-check the block starting at 15104 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_118 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15104 = true := by decide +kernel

/-- Kernel-check the block starting at 15232 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_119 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15232 = true := by decide +kernel

/-- Kernel-check the block starting at 15360 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_120 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15360 = true := by decide +kernel

/-- Kernel-check the block starting at 15488 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_121 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15488 = true := by decide +kernel

/-- Kernel-check the block starting at 15616 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_122 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15616 = true := by decide +kernel

/-- Kernel-check the block starting at 15744 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_123 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15744 = true := by decide +kernel

/-- Kernel-check the block starting at 15872 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_124 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 15872 = true := by decide +kernel

/-- Kernel-check the block starting at 16000 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_125 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 16000 = true := by decide +kernel

/-- Kernel-check the block starting at 16128 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_126 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 16128 = true := by decide +kernel

/-- Kernel-check the block starting at 16256 with 128 leaves.
Indices above 16000 are padding and contribute no numerical obligation. -/
private theorem gaussianResolvent_grid_block_127 :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 7 16256 = true := by decide +kernel

/-- The 128 kernel-checked blocks certify all 16384 leaves, including padding.
Combine their Boolean conjunctions without repeating the numerical reductions. -/
private theorem gaussianResolvent_grid_checked :
    gaussianBalancedGridCheck gaussianResolventGridPredicate 14 0 = true := by
  exact
    (Bool.and_eq_true _ _).mpr
      ⟨(Bool.and_eq_true _ _).mpr
          ⟨(Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_0, gaussianResolvent_grid_block_1⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_2, gaussianResolvent_grid_block_3⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_4, gaussianResolvent_grid_block_5⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_6, gaussianResolvent_grid_block_7⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_8, gaussianResolvent_grid_block_9⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_10, gaussianResolvent_grid_block_11⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_12, gaussianResolvent_grid_block_13⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_14, gaussianResolvent_grid_block_15⟩⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_16, gaussianResolvent_grid_block_17⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_18, gaussianResolvent_grid_block_19⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_20, gaussianResolvent_grid_block_21⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_22, gaussianResolvent_grid_block_23⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_24, gaussianResolvent_grid_block_25⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_26, gaussianResolvent_grid_block_27⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_28, gaussianResolvent_grid_block_29⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_30,
                                gaussianResolvent_grid_block_31⟩⟩⟩⟩⟩,
            (Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_32, gaussianResolvent_grid_block_33⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_34, gaussianResolvent_grid_block_35⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_36, gaussianResolvent_grid_block_37⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_38, gaussianResolvent_grid_block_39⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_40, gaussianResolvent_grid_block_41⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_42, gaussianResolvent_grid_block_43⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_44, gaussianResolvent_grid_block_45⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_46, gaussianResolvent_grid_block_47⟩⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_48, gaussianResolvent_grid_block_49⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_50, gaussianResolvent_grid_block_51⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_52, gaussianResolvent_grid_block_53⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_54, gaussianResolvent_grid_block_55⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_56, gaussianResolvent_grid_block_57⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_58, gaussianResolvent_grid_block_59⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_60, gaussianResolvent_grid_block_61⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_62,
                                gaussianResolvent_grid_block_63⟩⟩⟩⟩⟩⟩,
        (Bool.and_eq_true _ _).mpr
          ⟨(Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_64, gaussianResolvent_grid_block_65⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_66, gaussianResolvent_grid_block_67⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_68, gaussianResolvent_grid_block_69⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_70, gaussianResolvent_grid_block_71⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_72, gaussianResolvent_grid_block_73⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_74, gaussianResolvent_grid_block_75⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_76, gaussianResolvent_grid_block_77⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_78, gaussianResolvent_grid_block_79⟩⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_80, gaussianResolvent_grid_block_81⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_82, gaussianResolvent_grid_block_83⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_84, gaussianResolvent_grid_block_85⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_86, gaussianResolvent_grid_block_87⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_88, gaussianResolvent_grid_block_89⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_90, gaussianResolvent_grid_block_91⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_92, gaussianResolvent_grid_block_93⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_94,
                                gaussianResolvent_grid_block_95⟩⟩⟩⟩⟩,
            (Bool.and_eq_true _ _).mpr
              ⟨(Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_96, gaussianResolvent_grid_block_97⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_98, gaussianResolvent_grid_block_99⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_100, gaussianResolvent_grid_block_101⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_102,
                                gaussianResolvent_grid_block_103⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_104, gaussianResolvent_grid_block_105⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_106, gaussianResolvent_grid_block_107⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_108, gaussianResolvent_grid_block_109⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_110,
                                gaussianResolvent_grid_block_111⟩⟩⟩⟩,
                (Bool.and_eq_true _ _).mpr
                  ⟨(Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_112, gaussianResolvent_grid_block_113⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_114, gaussianResolvent_grid_block_115⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_116, gaussianResolvent_grid_block_117⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_118,
                                gaussianResolvent_grid_block_119⟩⟩⟩,
                    (Bool.and_eq_true _ _).mpr
                      ⟨(Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_120, gaussianResolvent_grid_block_121⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_122, gaussianResolvent_grid_block_123⟩⟩,
                        (Bool.and_eq_true _ _).mpr
                          ⟨(Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_124, gaussianResolvent_grid_block_125⟩,
                            (Bool.and_eq_true _ _).mpr
                              ⟨gaussianResolvent_grid_block_126,
                                gaussianResolvent_grid_block_127⟩⟩⟩⟩⟩⟩⟩

/-- Every node j/1000 with j≤16000 has scaled gap at least 9/100000.
Extract its successful Boolean check from the balanced block and apply soundness. -/
theorem gaussianResolvent_grid_lower (j : ℕ) (hj : j ≤ 16000) :
    (9 / 100000 : ℝ) ≤ gaussianResolventScaledGap ((j : ℝ) / 1000) := by
  have hb : j < 2 ^ (14 : ℕ) := Nat.lt_of_le_of_lt hj (by norm_num only : 16000 < 2 ^ (14 : ℕ))
  have h := gaussianBalancedGridCheck_sound _ 14 0 gaussianResolvent_grid_checked hb
  have hc : gaussianResolventNodeCheck j = true := by
    simpa only [Nat.zero_add, gaussianResolventGridPredicate, ite_eq_left hj] using h
  exact gaussianResolventNodeCheck_sound j hc

/-- The fixed rational majorant dominates the actual Gaussian kernel at every height.
All finite node checks, curvature, interpolation, evenness, and tail comparisons are proved. -/
theorem norm_gaussianGammaFunction_le_gaussianResolvent (t : ℝ) :
    ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤ gaussianResolventMajorant t := by
  exact norm_gaussianGammaFunction_le_gaussianResolvent_of_grid gaussianResolvent_grid_lower t

end PseudoPrime.Analysis
