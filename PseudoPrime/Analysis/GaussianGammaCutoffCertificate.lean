/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianGammaCutoffNodes
public import PseudoPrime.Analysis.GaussianGammaCutoffQuadrature

/-! # The finite Gaussian midpoint certificate and cutoff mass -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The sum of the 16,000 outward rounded node contributions, divided by 2000
cellwise. The midpoint at index k has numerator 2k+1-16000 over denominator 4000.
The result retains scale 10^40 and is executable using natural-number arithmetic. -/
def gaussianCutoffMidpointLower : ℕ :=
  ∑ k ∈ Finset.range 16000, gaussianCutoffNodeLower (((2 * k + 1 : ℕ) : ℤ) - 16000) / 2000

/-- The executable integer midpoint sum divided by its scale, minus the exact
curvature error 97/12000000, is a lower bound for the Gaussian cutoff mass.
Each node is analytically bounded and natural division rounds the cell contribution down.
This reduces the cutoff target to one finite integer comparison. -/
theorem gaussianCutoffMidpointLower_le_mass :
    (gaussianCutoffMidpointLower : ℝ) / gaussianCutoffNodeScale - 97 / 12000000 ≤
      ∫ u in (0 : ℝ)..(21 / 10), gaussianGammaProfile u / Real.sqrt u := by
  have hpoint (k : ℕ) (hk : k ∈ Finset.range 16000) :
    ((gaussianCutoffNodeLower (((2 * k + 1 : ℕ) : ℤ) - 16000) / 2000 : ℕ) : ℝ) ≤
      (gaussianCutoffNodeScale : ℝ) *
        ((1 / 2000 : ℝ) *
          gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000))) := by
    have hkr : (k : ℝ) ≤ 15999 := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hm : |((((2 * k + 1 : ℕ) : ℤ) - 16000 : ℤ) : ℝ)| ≤ 16000 := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      exact abs_le.mpr ⟨by linarith only [hkn], by linarith only [hkr]⟩
    have hn := gaussianCutoffNodeLower_le (((2 * k + 1 : ℕ) : ℤ) - 16000) hm
    have hx :
      (((((2 * k + 1 : ℕ) : ℤ) - 16000 : ℤ) : ℝ) / 4000) = -4 + ((k : ℝ) + 1 / 2) * (1 / 2000) := by
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast,
        Int.cast_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
      ring
    rw [hx] at hn
    have hd := div_le_div_of_nonneg_right hn (by norm_num only : (0 : ℝ) ≤ 2000)
    have hf :=
      (Nat.cast_div_le (m := gaussianCutoffNodeLower (((2 * k + 1 : ℕ) : ℤ) - 16000)) (n := 2000) :
        ((gaussianCutoffNodeLower (((2 * k + 1 : ℕ) : ℤ) - 16000) / 2000 : ℕ) : ℝ) ≤ _)
    norm_num only [Nat.cast_ofNat] at hf
    have he :
      (gaussianCutoffNodeScale : ℝ) *
            gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000)) /
          2000 =
        (gaussianCutoffNodeScale : ℝ) *
          ((1 / 2000 : ℝ) *
            gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000))) := by
      ring
    exact hf.trans (hd.trans_eq he)
  have hs := Finset.sum_le_sum hpoint
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hscale : (0 : ℝ) < gaussianCutoffNodeScale := by norm_num only [gaussianCutoffNodeScale]
  have hsum :
    (gaussianCutoffMidpointLower : ℝ) / gaussianCutoffNodeScale ≤
      (1 / 2000 : ℝ) *
        ∑ k ∈ Finset.range 16000,
          gaussianGammaCutoffIntegrand (21 / 10) (-4 + ((k : ℝ) + 1 / 2) * (1 / 2000)) := by
    apply (div_le_iff₀ hscale).mpr
    simpa only [gaussianCutoffMidpointLower, Nat.cast_sum, mul_comm] using hs
  exact (sub_le_sub_right hsum (97 / 12000000)).trans gaussianGammaCutoff_midpoint_16000_lower

end PseudoPrime.Analysis
