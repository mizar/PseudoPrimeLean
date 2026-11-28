/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceSignCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ReflectionCert
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCompIntegerBernstein
import PseudoPrime.Analysis.BernsteinBounds

/-! # K186 profile signs over the finite high window -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On an integer cell, check a common lower bound for the Bernstein row. -/
private def k186HighLower (a w low : ℤ) : Bool :=
  let B := baseRow.affine 83 a w 1
  let D := B.den * ((83 : ℕ).factorial : ℤ)
  (List.range 84).all (fun j ↦ decide (low * D ≤ B.bernsteinNum 83 j))

/-- The affine row bound certifies the physical profile on the whole cell. -/
private theorem k186_high_lower_sound (a w low : ℤ) (hw : 0 < w)
    (h : k186HighLower a w low = true) :
    ∀ t ∈ Set.Icc (a : ℝ) ((a : ℝ) + (w : ℝ)),
      (low : ℝ) ≤ HighGaussianKernel.k186.realProfile.eval t := by
  have h₀ : (a : ℚ) < (a : ℚ) + (w : ℚ) := lt_add_of_pos_right _ (Int.cast_pos.mpr hw)
  have hp : HighGaussianKernel.k186.ratProfile.natDegree ≤ 83 := high_rat_profile_degree .k186
  have hbase := baseRow.poly_affine 83 a w 1 (by decide +kernel) (by decide)
  rw [base_row_poly] at hbase
  simp only [Int.cast_one, div_one] at hbase
  have hs (j : Fin 84) :
    (low : ℚ) ≤
      Analysis.bernsteinRatCoeff
        (HighGaussianKernel.k186.ratProfile.comp
          (Polynomial.C (w : ℚ) * Polynomial.X + Polynomial.C (a : ℚ)))
        83 j := by
    have hj := of_decide_eq_true (List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt))
    rw [← hbase, MiddleIntRow.bernstein_num_eq]
    have hden : 0 < (baseRow.affine 83 a w 1).den := by
      change 0 < baseRow.den * (1 : ℤ) ^ 83
      exact mul_pos (by decide +kernel) (pow_pos zero_lt_one _)
    have hscale : (0 : ℚ) < ((baseRow.affine 83 a w 1).den : ℚ) * ((83 : ℕ).factorial : ℚ) :=
      mul_pos (Int.cast_pos.mpr hden) (Nat.cast_pos.mpr (Nat.factorial_pos _))
    apply (le_div_iff₀ hscale).mpr
    exact_mod_cast hj
  intro t ht
  obtain ⟨v, hv⟩ :=
    sign_cell_bernstein_eval _ hp h₀ (by simpa only [Rat.cast_add, Rat.cast_intCast] using ht)
  rw [high_comp_profile_map, add_sub_cancel_left] at hv
  rw [hv]
  apply Analysis.le_bernstein_sum
  intro j
  exact_mod_cast hs j

/-- A single sign check covers the first finite high range. Thus the two
Gamma convolutions can reuse their lower bounds at the left endpoint. -/
public theorem k186_profile_nonneg_35_57 {t : ℝ} (ht : t ∈ Set.Icc (35 : ℝ) 57) :
    0 ≤ HighGaussianKernel.k186.realProfile.eval t := by
  have h := k186_high_lower_sound 35 22 0 (by decide) (by decide +kernel)
  simp only [Int.cast_ofNat, Int.cast_zero] at h
  exact h t (by simpa only [show (35 : ℝ) + 22 = 57 by norm_num only] using ht)

/-- The entire initial convolution prefix has a single coarse lower bound.
The factor at the finite high-window entrance makes its charge small. -/
public theorem k186_profile_lower_to35 {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 35) :
    -(10 ^ 35 : ℝ) ≤ HighGaussianKernel.k186.realProfile.eval t := by
  have h := k186_high_lower_sound 0 35 (-(10 ^ 35)) (by decide) (by decide +kernel)
  simp only [Int.cast_ofNat, Int.cast_zero, Int.cast_neg, Int.cast_pow, zero_add] at h
  exact h t ht

/-- Across the final finite sign transitions, one Bernstein row supplies a
coarse lower bound for the exponentially damped convolution tails. -/
public theorem k186_profile_lower_57_65 {t : ℝ} (ht : t ∈ Set.Icc (57 : ℝ) 65) :
    -(10 ^ 61 : ℝ) ≤ HighGaussianKernel.k186.realProfile.eval t := by
  have h := k186_high_lower_sound 57 8 (-(10 ^ 61)) (by decide) (by decide +kernel)
  simp only [Int.cast_ofNat, Int.cast_neg, Int.cast_pow,
    show (57 : ℝ) + 8 = 65 by norm_num only] at h
  exact h t ht

end PseudoPrime.PrimeTestBounds.MillerRabin
