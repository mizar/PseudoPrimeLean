/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPsiRowsLower

/-! # Certified Chebyshev lower bound on a finite interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_40000 : (40012 : ℚ) ≤ ((centerRowsBelow 40000).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_40512 : (40479 : ℚ) ≤ ((centerRowsBelow 40512).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_41024 : (40978 : ℚ) ≤ ((centerRowsBelow 41024).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_41536 : (41499 : ℚ) ≤ ((centerRowsBelow 41536).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_42048 : (42073 : ℚ) ≤ ((centerRowsBelow 42048).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- Checked prime-power prefixes imply `x - 600 ≤ psi x` throughout
`[40000, 42560)`. Monotonicity transfers each prefix to its half-open cell. -/
theorem psi_lower_40000_42560 {x : ℝ} (ha : 40000 ≤ x) (hb : x < 42560) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h40512 : x < 40512
  · have hstart : (40000 : ℝ) ≤ x := ha
    have hp : (40012 : ℝ) ≤ Chebyshev.psi 40000 :=
      quarter_psi_rows_lower (by decide) 40012 rows_40000
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h40512]
  by_cases h41024 : x < 41024
  · have hstart : (40512 : ℝ) ≤ x := by linarith only [h40512]
    have hp : (40479 : ℝ) ≤ Chebyshev.psi 40512 :=
      quarter_psi_rows_lower (by decide) 40479 rows_40512
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h41024]
  by_cases h41536 : x < 41536
  · have hstart : (41024 : ℝ) ≤ x := by linarith only [h41024]
    have hp : (40978 : ℝ) ≤ Chebyshev.psi 41024 :=
      quarter_psi_rows_lower (by decide) 40978 rows_41024
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h41536]
  by_cases h42048 : x < 42048
  · have hstart : (41536 : ℝ) ≤ x := by linarith only [h41536]
    have hp : (41499 : ℝ) ≤ Chebyshev.psi 41536 :=
      quarter_psi_rows_lower (by decide) 41499 rows_41536
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h42048]
  have hstart : (42048 : ℝ) ≤ x := by linarith only [h42048]
  have hp : (42073 : ℝ) ≤ Chebyshev.psi 42048 := quarter_psi_rows_lower (by decide) 42073 rows_42048
  have hm := Chebyshev.psi_mono hstart
  linarith only [hp, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
