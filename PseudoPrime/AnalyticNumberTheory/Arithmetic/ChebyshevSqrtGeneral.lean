/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import PseudoPrime.Analysis.FloorIntervalBounds

/-! # Endpoint estimates for general square-root error bounds -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For `c ≤ 2`, the lower crossing function `t - c √t` is nondecreasing on `[1, ∞)`.
The proof compares the square roots and factors the difference of their squares. -/
private theorem sub_sqrt_mono_of_le_two {c : ℝ} (hc : c ≤ 2) :
    MonotoneOn (fun t : ℝ ↦ t - c * Real.sqrt t) (Set.Ici 1) := by
  intro x hx y hy hxy
  change (1 : ℝ) ≤ x at hx
  change (1 : ℝ) ≤ y at hy
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hy0 : 0 ≤ y := by linarith only [hy]
  have hsx := Real.sq_sqrt hx0
  have hsy := Real.sq_sqrt hy0
  have hsx1 : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    simpa only [Real.sqrt_one] using h
  have hsy1 : 1 ≤ Real.sqrt y := by
    have h := Real.sqrt_le_sqrt hy
    simpa only [Real.sqrt_one] using h
  have hs := Real.sqrt_le_sqrt hxy
  have hm :=
    mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ Real.sqrt x + Real.sqrt y - c by linarith only [hsx1, hsy1, hc])
  nlinarith only [hsx, hsy, hm]

/-- For `0 ≤ c ≤ 2`, certified psi values and crossing inequalities at integer endpoints give
`|psi x - x| ≤ c √x` on the half-open cell `[a, b)`, provided `1 ≤ a`. The floor-invariance of
psi controls the right endpoint; the monotonic crossing functions extend the bounds to every real
point in the cell. This is used by finite certificates with different coefficients. -/
theorem psi_sqrt_cross_cell {a b : ℕ} {lo hi ca cb c x : ℝ} (hc0 : 0 ≤ c) (hc2 : c ≤ 2)
    (ha : (1 : ℝ) ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x < b) (hl : lo ≤ Chebyshev.psi a)
    (hu : Chebyshev.psi (b - 1 : ℕ) ≤ hi) (hca : ca ≤ c * Real.sqrt a) (hcb : cb ≤ c * Real.sqrt b)
    (hcrossl : (b : ℝ) ≤ lo + cb) (hcrossu : hi ≤ (a : ℝ) + ca) :
    |Chebyshev.psi x - x| ≤ c * Real.sqrt x := by
  apply
    Analysis.halfopen_error_of_endpoints Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor hax hxb
      ?_ ?_ hl hu hca hcb hcrossl hcrossu
  · apply (sub_sqrt_mono_of_le_two hc2).mono
    intro t ht
    exact ha.trans ht.1
  · intro u hu v hv huv
    have hs := Real.sqrt_le_sqrt huv
    have hm := mul_le_mul_of_nonneg_left hs hc0
    linarith only [huv, hm]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
