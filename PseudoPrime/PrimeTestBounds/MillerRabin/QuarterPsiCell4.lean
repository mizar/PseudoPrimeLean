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
private theorem rows_47680 : (47616 : ℚ) ≤ ((centerRowsBelow 47680).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_48192 : (48122 : ℚ) ≤ ((centerRowsBelow 48192).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_48704 : (48629 : ℚ) ≤ ((centerRowsBelow 48704).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_49216 : (49191 : ℚ) ≤ ((centerRowsBelow 49216).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_49728 : (49688 : ℚ) ≤ ((centerRowsBelow 49728).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- Checked prime-power prefixes imply `x - 600 ≤ psi x` throughout
`[47680, 50000)`. Monotonicity transfers each prefix to its half-open cell. -/
theorem psi_lower_47680_50000 {x : ℝ} (ha : 47680 ≤ x) (hb : x < 50000) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h48192 : x < 48192
  · have hstart : (47680 : ℝ) ≤ x := ha
    have hp : (47616 : ℝ) ≤ Chebyshev.psi 47680 :=
      quarter_psi_rows_lower (by decide) 47616 rows_47680
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h48192]
  by_cases h48704 : x < 48704
  · have hstart : (48192 : ℝ) ≤ x := by linarith only [h48192]
    have hp : (48122 : ℝ) ≤ Chebyshev.psi 48192 :=
      quarter_psi_rows_lower (by decide) 48122 rows_48192
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h48704]
  by_cases h49216 : x < 49216
  · have hstart : (48704 : ℝ) ≤ x := by linarith only [h48704]
    have hp : (48629 : ℝ) ≤ Chebyshev.psi 48704 :=
      quarter_psi_rows_lower (by decide) 48629 rows_48704
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h49216]
  by_cases h49728 : x < 49728
  · have hstart : (49216 : ℝ) ≤ x := by linarith only [h49216]
    have hp : (49191 : ℝ) ≤ Chebyshev.psi 49216 :=
      quarter_psi_rows_lower (by decide) 49191 rows_49216
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h49728]
  have hstart : (49728 : ℝ) ≤ x := by linarith only [h49728]
  have hp : (49688 : ℝ) ≤ Chebyshev.psi 49728 := quarter_psi_rows_lower (by decide) 49688 rows_49728
  have hm := Chebyshev.psi_mono hstart
  linarith only [hp, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
