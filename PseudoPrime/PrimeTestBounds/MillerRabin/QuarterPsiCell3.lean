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
private theorem rows_45120 : (45123 : ℚ) ≤ ((centerRowsBelow 45120).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_45632 : (45627 : ℚ) ≤ ((centerRowsBelow 45632).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_46144 : (46099 : ℚ) ≤ ((centerRowsBelow 46144).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_46656 : (46615 : ℚ) ≤ ((centerRowsBelow 46656).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_47168 : (47110 : ℚ) ≤ ((centerRowsBelow 47168).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- Checked prime-power prefixes imply `x - 600 ≤ psi x` throughout
`[45120, 47680)`. Monotonicity transfers each prefix to its half-open cell. -/
theorem psi_lower_45120_47680 {x : ℝ} (ha : 45120 ≤ x) (hb : x < 47680) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h45632 : x < 45632
  · have hstart : (45120 : ℝ) ≤ x := ha
    have hp : (45123 : ℝ) ≤ Chebyshev.psi 45120 :=
      quarter_psi_rows_lower (by decide) 45123 rows_45120
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h45632]
  by_cases h46144 : x < 46144
  · have hstart : (45632 : ℝ) ≤ x := by linarith only [h45632]
    have hp : (45627 : ℝ) ≤ Chebyshev.psi 45632 :=
      quarter_psi_rows_lower (by decide) 45627 rows_45632
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h46144]
  by_cases h46656 : x < 46656
  · have hstart : (46144 : ℝ) ≤ x := by linarith only [h46144]
    have hp : (46099 : ℝ) ≤ Chebyshev.psi 46144 :=
      quarter_psi_rows_lower (by decide) 46099 rows_46144
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h46656]
  by_cases h47168 : x < 47168
  · have hstart : (46656 : ℝ) ≤ x := by linarith only [h46656]
    have hp : (46615 : ℝ) ≤ Chebyshev.psi 46656 :=
      quarter_psi_rows_lower (by decide) 46615 rows_46656
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h47168]
  have hstart : (47168 : ℝ) ≤ x := by linarith only [h47168]
  have hp : (47110 : ℝ) ≤ Chebyshev.psi 47168 := quarter_psi_rows_lower (by decide) 47110 rows_47168
  have hm := Chebyshev.psi_mono hstart
  linarith only [hp, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
