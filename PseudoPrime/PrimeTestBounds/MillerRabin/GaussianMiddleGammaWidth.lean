/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleGammaBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntTransforms

import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailCert

/-! # Integer dot-product certificates for middle Gamma coefficient widths -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Pair a centered integer profile row with the rounded radius weights. -/
@[expose]
def middleGammaWidthDot (row : MiddleIntRow) (N : ℕ) (w : ℕ → ℤ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), |row.num k| * w k

/-- The integer dot product encloses the rational width correction after
division by the two positive row denominators. -/
theorem middle_gamma_width_int_le (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : 0 < r.den) (hb : 0 < b)
    (h : ℚ) (g : ℕ → ℚ × ℚ) (w : ℕ → ℤ) {D : ℤ} (hD : 0 < D)
    (hw : ∀ k ≤ N, middleGammaWidthWeight h g k ≤ (w k : ℚ) / D) (hw₀ : ∀ k ≤ N, 0 ≤ w k) :
    let s := r.shift N a b
    middleGammaWidthBudget (r.poly N) ((a : ℚ) / b) h g ≤
      (middleGammaWidthDot s N w : ℚ) / ((s.den : ℚ) * D) := by
  intro s
  have hdeg : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hs : s.poly N = Polynomial.taylor ((a : ℚ) / b) (r.poly N) := by
    rw [Polynomial.taylor_apply]
    exact r.poly_shift N a b hr.ne' hb.ne'
  have hden : 0 < s.den := mul_pos hr (pow_pos hb _)
  refine
    (middle_gamma_width_dot_le (r.poly N) ((a : ℚ) / b) h g hdeg (fun k ↦ (w k : ℚ) / D) hw
          (fun k hk ↦
            div_nonneg (Int.cast_nonneg_iff.mpr (hw₀ k hk))
              (Int.cast_nonneg_iff.mpr hD.le))).trans_eq
      ?_
  rw [← hs]
  simp only [middleGammaWidthDot, Int.cast_sum, Int.cast_mul, Int.cast_abs, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [s.poly_coeff (Nat.le_of_lt_succ (Finset.mem_range.mp hk)), abs_div,
    abs_of_pos (Int.cast_pos.mpr hden), div_mul_div_comm]

/-- A checked integer comparison bounds the width budget by a prescribed
rational cap. The kernel compares products of integers at this step. -/
theorem middle_gamma_width_int_cap (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : 0 < r.den)
    (hb : 0 < b) (h : ℚ) (g : ℕ → ℚ × ℚ) (w : ℕ → ℤ) {D u v : ℤ} (hD : 0 < D) (hv : 0 < v)
    (hw : ∀ k ≤ N, middleGammaWidthWeight h g k ≤ (w k : ℚ) / D) (hw₀ : ∀ k ≤ N, 0 ≤ w k)
    (hc : middleGammaWidthDot (r.shift N a b) N w * v ≤ u * ((r.shift N a b).den * D)) :
    middleGammaWidthBudget (r.poly N) ((a : ℚ) / b) h g ≤ (u : ℚ) / v := by
  refine (middle_gamma_width_int_le r N a b hr hb h g w hD hw hw₀).trans ?_
  have hden : 0 < (r.shift N a b).den := mul_pos hr (pow_pos hb _)
  apply
    (div_le_div_iff₀ (mul_pos (Int.cast_pos.mpr hden) (Int.cast_pos.mpr hD))
        (Int.cast_pos.mpr hv)).mpr
  exact_mod_cast hc

/-- A rational exponential cap using one factor per full unit and a
separate factor for the remaining fortieths. -/
@[expose]
def middleGammaExpCap (ticks : ℕ) : ℚ :=
  (36788 / 100000 : ℚ) ^ (ticks / 40) * (97531 / 100000 : ℚ) ^ (ticks % 40)

/-- The short rational exponentiation encloses the negative exponential
at every nonnegative number of fortieths. -/
theorem middle_gamma_exp_cap (ticks : ℕ) :
    Real.exp (-(ticks : ℝ) / 40) ≤ (middleGammaExpCap ticks : ℝ) := by
  have h₀ :=
    middle_exp_neg_le_of_taylor (t := 1) (R := 36788 / 100000) 11 (by norm_num only)
      (by norm_num only) (by decide +kernel)
  have h₁ :=
    middle_exp_neg_le_of_taylor (t := 1 / 40) (R := 97531 / 100000) 5 (by norm_num only)
      (by norm_num only) (by decide +kernel)
  have ht : (ticks : ℝ) = (ticks / 40 : ℕ) * (40 : ℝ) + (ticks % 40 : ℕ) := by
    exact_mod_cast
      (show ticks = ticks / 40 * 40 + ticks % 40 by
        rw [Nat.mul_comm (ticks / 40) 40, Nat.div_add_mod])
  have he :
    -(ticks : ℝ) / 40 = (ticks / 40 : ℕ) * (-(1 : ℝ)) + (ticks % 40 : ℕ) * (-(1 / 40 : ℝ)) := by
    rw [ht]
    ring
  rw [he, Real.exp_add, Real.exp_natCast_mul, Real.exp_natCast_mul]
  simp only [middleGammaExpCap, Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one] at h₀ h₁ ⊢
  exact
    mul_le_mul (pow_le_pow_left₀ (Real.exp_pos _).le h₀ _)
      (pow_le_pow_left₀ (Real.exp_pos _).le h₁ _) (pow_nonneg (Real.exp_pos _).le _)
      (pow_nonneg (by norm_num only) _)

/-- Transfer a rational width certificate to a physical cap on any height
whose exponent is at least the certified number of fortieths. -/
theorem middle_gamma_width_scaled {κ cap R : ℚ} {y A : ℝ} (ticks : ℕ) (hκ : 0 ≤ κ) (hcap : 0 ≤ cap)
    (hy : (ticks : ℝ) / 40 ≤ y) (hA : A ≤ cap) (hn : κ * middleGammaExpCap ticks * cap ≤ R) :
    (κ : ℝ) * Real.exp (-y) * A ≤ (R : ℝ) := by
  have hE :=
    (Real.exp_le_exp.mpr (neg_le_neg hy)).trans
      (by simpa only [neg_div] using middle_gamma_exp_cap ticks)
  have hκ' : (0 : ℝ) ≤ κ := Rat.cast_nonneg.mpr hκ
  calc
    _ ≤ (κ : ℝ) * Real.exp (-y) * (cap : ℝ) :=
      mul_le_mul_of_nonneg_left hA (mul_nonneg hκ' (Real.exp_pos _).le)
    _ ≤ (κ : ℝ) * (middleGammaExpCap ticks : ℝ) * (cap : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hκ') (Rat.cast_nonneg.mpr hcap)
    _ ≤ _ := by simpa only [Rat.cast_mul] using (Rat.cast_le (K := ℝ)).mpr hn

end PseudoPrime.PrimeTestBounds.MillerRabin
