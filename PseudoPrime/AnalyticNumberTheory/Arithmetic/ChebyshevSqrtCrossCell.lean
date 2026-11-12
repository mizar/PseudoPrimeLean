/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import PseudoPrime.Analysis.FloorIntervalBounds

/-! # Endpoint certificates for a square-root Chebyshev error -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The lower crossing function for the `4/5` square-root envelope is
monotone on `[1, ∞)`. Squaring the square roots reduces the claim to the
nonnegativity of a product. -/
private theorem sub_sqrt_mono :
    MonotoneOn (fun t : ℝ ↦ t - (4 / 5 : ℝ) * Real.sqrt t) (Set.Ici 1) := by
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
  have hs := Real.sqrt_le_sqrt hxy
  have hm :=
    mul_nonneg (sub_nonneg.mpr hs)
      (show 0 ≤ Real.sqrt x + Real.sqrt y - 4 / 5
        by
        have h := Real.sqrt_nonneg y
        linarith only [hsx1, h])
  nlinarith only [hsx, hsy, hm]

/-- Certified psi bounds at the endpoints and two crossing inequalities imply
`|psi x - x| ≤ (4/5) sqrt x` throughout the half-open integer cell `[a, b)`.
The endpoint bounds and the lower bounds on the envelope are explicit inputs. -/
theorem psi_four_fifths_cross_cell {a b : ℕ} {lo hi ca cb x : ℝ} (ha : (1 : ℝ) ≤ a)
    (hax : (a : ℝ) ≤ x) (hxb : x < b) (hl : lo ≤ Chebyshev.psi a)
    (hu : Chebyshev.psi (b - 1 : ℕ) ≤ hi) (hca : ca ≤ (4 / 5 : ℝ) * Real.sqrt a)
    (hcb : cb ≤ (4 / 5 : ℝ) * Real.sqrt b) (hcrossl : (b : ℝ) ≤ lo + cb)
    (hcrossu : hi ≤ (a : ℝ) + ca) : |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  apply
    Analysis.halfopen_error_of_endpoints Chebyshev.psi_mono Chebyshev.psi_eq_psi_coe_floor hax hxb
      ?_ ?_ hl hu hca hcb hcrossl hcrossu
  · apply sub_sqrt_mono.mono
    intro t ht
    exact ha.trans ht.1
  · intro u hu v hv huv
    have hs := Real.sqrt_le_sqrt huv
    have hm := mul_le_mul_of_nonneg_left hs (show (0 : ℝ) ≤ 4 / 5 by norm_num only)
    linarith only [huv, hm]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
