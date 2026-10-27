/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffExecution
public import PseudoPrime.Analysis.GaussianGammaCutoffQuadrature

/-! # Kernel certificate for the Gaussian cutoff at 6/5 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The 128 midpoint contributions for cutoff 6/5, each rounded down after division
by the grid denominator. The coordinate numerator is `125 * (2k + 1 - 128)`. -/
def gaussianCutoffSixFifthsMidpointLower : ℕ :=
  ∑ k ∈ Finset.range 128,
    gaussianCutoffNodeLowerParamFast 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128)) / 16

/-- Exact scale-10^40 value of the 128-node midpoint certificate, checked by the kernel. -/
theorem gaussianCutoffSixFifthsMidpointLower_value :
    gaussianCutoffSixFifthsMidpointLower = 6451458606530160077299492728763448252331 := by
  decide +kernel

/-- The certified scale value minus the exact curvature error exceeds 16/25. -/
theorem gaussianCutoffSixFifthsMidpointLower_gt :
    (gaussianCutoffSixFifthsMidpointLower : ℝ) / gaussianCutoffNodeScale - 1 / 288 > 16 / 25 := by
  rw [gaussianCutoffSixFifthsMidpointLower_value]
  norm_num only [gaussianCutoffNodeScale]

/-- The kernel-checked midpoint certificate proves a strict mass lower bound at 6/5. -/
theorem gaussianGammaCutoffSixFifths_mass_gt :
    16 / 25 < ∫ u in (0 : ℝ)..(6 / 5), gaussianGammaProfile u / Real.sqrt u := by
  have hmid := gaussianGammaCutoff_midpoint_128_lower
  have hnum :
    (gaussianCutoffSixFifthsMidpointLower : ℝ) / gaussianCutoffNodeScale - 1 / 288 ≤
      (1 / 16 : ℝ) *
          (∑ k ∈ Finset.range 128,
            gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16))) -
        1 / 288 := by
    have hpoint (k : ℕ) (hk : k ∈ Finset.range 128) :
      ((gaussianCutoffNodeLowerParamFast 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128)) / 16 : ℕ) : ℝ) ≤
        (gaussianCutoffNodeScale : ℝ) *
          ((1 / 16 : ℝ) *
            gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16))) := by
      have hk' : k < 128 := Finset.mem_range.mp hk
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hkmax : (k : ℝ) ≤ 127 := by exact_mod_cast Nat.le_of_lt_succ hk'
      have hm : |((125 * (((2 * k + 1 : ℕ) : ℤ) - 128) : ℤ) : ℝ)| ≤ 16000 := by
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat, Int.cast_natCast,
          Int.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        rw [abs_le]
        constructor <;> nlinarith only [hk0, hkmax]
      have hn := gaussianCutoffNodeLowerParamFast_eq 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128))
      rw [hn]
      have ha := gaussianCutoffNodeLowerParam_le 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128)) hm
      have hx :
        (((125 * (((2 * k + 1 : ℕ) : ℤ) - 128) : ℤ) : ℝ) / 4000) =
          -4 + ((k : ℝ) + 1 / 2) * (1 / 16) := by
        simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_ofNat, Int.cast_natCast,
          Int.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
        ring
      rw [hx] at ha
      have hd := div_le_div_of_nonneg_right ha (by norm_num only : (0 : ℝ) ≤ 16)
      have hf :
        ((gaussianCutoffNodeLowerParamFast 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128)) / 16 : ℕ) :
            ℝ) ≤
          (gaussianCutoffNodeLowerParamFast 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128)) : ℕ) / 16 :=
        Nat.cast_div_le (m :=
          gaussianCutoffNodeLowerParamFast 6 5 (125 * (((2 * k + 1 : ℕ) : ℤ) - 128))) (n := 16)
      rw [hn] at hf
      have he :
        (gaussianCutoffNodeScale : ℝ) *
              gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16)) /
            16 =
          (gaussianCutoffNodeScale : ℝ) *
            ((1 / 16 : ℝ) *
              gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16))) := by
        ring
      exact hf.trans (hd.trans_eq he)
    have hs := Finset.sum_le_sum hpoint
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
    have hscale : (0 : ℝ) < gaussianCutoffNodeScale := by norm_num only [gaussianCutoffNodeScale]
    have hs' :
      (gaussianCutoffSixFifthsMidpointLower : ℝ) ≤
        gaussianCutoffNodeScale *
          ((1 / 16 : ℝ) *
            ∑ k ∈ Finset.range 128,
              gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16))) := by
      simpa only [gaussianCutoffSixFifthsMidpointLower, Nat.cast_sum, mul_comm] using hs
    have hs'' :
      (gaussianCutoffSixFifthsMidpointLower : ℝ) / gaussianCutoffNodeScale ≤
        (1 / 16 : ℝ) *
          ∑ k ∈ Finset.range 128,
            gaussianGammaCutoffIntegrand (6 / 5) (-4 + ((k : ℝ) + 1 / 2) * (1 / 16)) := by
      apply (div_le_iff₀ hscale).2
      simpa only [mul_comm] using hs'
    exact sub_le_sub_right hs'' (1 / 288)
  exact lt_of_lt_of_le gaussianCutoffSixFifthsMidpointLower_gt (hnum.trans hmid)

end PseudoPrime.Analysis
