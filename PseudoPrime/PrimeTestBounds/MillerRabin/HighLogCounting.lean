/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Combinatorics.FactorialPairBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Logarithmic conversion of paired binomial estimates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the paired base is positive and its `k`-fold logarithm exceeds `T`,
then `log (choose M k) > T`. Apply logarithm monotonicity to the paired
binomial lower bound; this converts the high-range scalar budget to a
kernel count without evaluating the binomial coefficient. -/
theorem log_choose_gt_of_paired_budget (M k : ℕ) {T : ℝ}
    (hR : 0 < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))
    (hcount : T < k * Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))) :
    T < Real.log (Nat.choose M k : ℝ) := by
  have hp := pow_pos hR k
  have hl := Real.log_le_log hp (Combinatorics.paired_choose_real_lower M k)
  rw [Real.log_pow] at hl
  exact hcount.trans_le hl

/-- Under the same positive-base logarithmic budget, the binomial coefficient
strictly exceeds `exp T`. Exponentiate the scalar inequality and apply the
paired binomial lower bound. This is the high-range kernel-size interface. -/
theorem exp_lt_choose_of_paired_budget (M k : ℕ) {T : ℝ}
    (hR : 0 < 2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))
    (hcount : T < k * Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1))) :
    Real.exp T < (Nat.choose M k : ℝ) := by
  have he := Real.exp_lt_exp.mpr hcount
  rw [show
      (k : ℝ) * Real.log (2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) =
        Real.log ((2 * ((M + 1 - k : ℕ) : ℝ) / (k + 1)) ^ k)
      by rw [Real.log_pow]] at he
  rw [Real.exp_log (pow_pos hR _)] at he
  exact he.trans_le (Combinatorics.paired_choose_real_lower M k)

/-- For positive `x`, the natural number `ceil x - 1` lies in `[x - 1, x)`.
The strict upper bound also holds when `x` is an integer. This is the exponent
choice used to keep high-range prime products strictly below the local modulus. -/
theorem ceil_sub_one_bounds {x : ℝ} (hx : 0 < x) :
    x - 1 ≤ (⌈x⌉₊ - 1 : ℕ) ∧ ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := by
  have hcpos : 0 < ⌈x⌉₊ := Nat.ceil_pos.mpr hx
  have hc : (⌈x⌉₊ - 1 : ℕ) + 1 = ⌈x⌉₊ := Nat.sub_add_cancel hcpos
  have hlt : (⌈x⌉₊ - 1 : ℕ) < ⌈x⌉₊ := Nat.sub_lt hcpos (by norm_num only)
  have hupper : ((⌈x⌉₊ - 1 : ℕ) : ℝ) < x := Nat.lt_ceil.mp hlt
  have hceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have he : ((⌈x⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈x⌉₊ : ℝ) := by exact_mod_cast hc
  constructor
  · linarith only [hceil, he]
  · exact hupper

/-- For `L ≥ 1024`, the floor of `(2 / 3) * L` is above `(2 / 3) * L - 1`,
at least `L / 2`, and at least 56. These bounds supply the hypotheses for
the high-range prime-count and paired-factor estimates. -/
theorem high_radius_floor_lower {L : ℝ} (hL : 1024 ≤ L) :
    (2 / 3 : ℝ) * L - 1 < (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) ∧
      L / 2 ≤ (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) ∧ 56 ≤ ⌊(2 / 3 : ℝ) * L⌋₊ := by
  have hf := Nat.lt_floor_add_one ((2 / 3 : ℝ) * L)
  have hlo : (2 / 3 : ℝ) * L - 1 < (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by linarith only [hf]
  have hh : L / 2 ≤ (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by linarith only [hL, hlo]
  have h56 : (56 : ℝ) ≤ (⌊(2 / 3 : ℝ) * L⌋₊ : ℝ) := by linarith only [hL, hh]
  exact
    ⟨hlo, hh,
      Nat.cast_le.mp
        (by
          norm_num only [Nat.cast_ofNat] at h56 ⊢; exact h56)⟩

/-- If `0 < y < x`, the exponent `ceil y - 1` is at most `floor x`.
The strict ceiling bound and floor's upper error bound yield a strict
comparison with `floor x + 1`. This validates natural subtraction in the
paired coefficient when `x` is the prime supply and `y` the log budget. -/
theorem ceil_sub_one_le_floor {x y : ℝ} (hy : 0 < y) (hxy : y < x) : ⌈y⌉₊ - 1 ≤ ⌊x⌋₊ := by
  have hk := (ceil_sub_one_bounds hy).2
  have hM := Nat.lt_floor_add_one x
  have hlt : ((⌈y⌉₊ - 1 : ℕ) : ℝ) < (⌊x⌋₊ : ℝ) + 1 := by linarith only [hk, hxy, hM]
  have hn : ⌈y⌉₊ - 1 < ⌊x⌋₊ + 1 := by exact_mod_cast hlt
  exact Nat.lt_succ_iff.mp hn

end PseudoPrime.PrimeTestBounds.MillerRabin
