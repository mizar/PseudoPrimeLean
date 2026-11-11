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
private theorem rows_42560 : (42638 : ℚ) ≤ ((centerRowsBelow 42560).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_43072 : (43192 : ℚ) ≤ ((centerRowsBelow 43072).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_43584 : (43598 : ℚ) ≤ ((centerRowsBelow 43584).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_44096 : (44122 : ℚ) ≤ ((centerRowsBelow 44096).map (fun r ↦ r.lo)).sum := by
  decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
-- Kernel reduction checks the filtered prime-power prefix.
private theorem rows_44608 : (44619 : ℚ) ≤ ((centerRowsBelow 44608).map (fun r ↦ r.lo)).sum := by
  decide +kernel

/-- Checked prime-power prefixes imply `x - 600 ≤ psi x` throughout
`[42560, 45120)`. Monotonicity transfers each prefix to its half-open cell. -/
theorem psi_lower_42560_45120 {x : ℝ} (ha : 42560 ≤ x) (hb : x < 45120) :
    x - 600 ≤ Chebyshev.psi x := by
  by_cases h43072 : x < 43072
  · have hstart : (42560 : ℝ) ≤ x := ha
    have hp : (42638 : ℝ) ≤ Chebyshev.psi 42560 :=
      quarter_psi_rows_lower (by decide) 42638 rows_42560
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h43072]
  by_cases h43584 : x < 43584
  · have hstart : (43072 : ℝ) ≤ x := by linarith only [h43072]
    have hp : (43192 : ℝ) ≤ Chebyshev.psi 43072 :=
      quarter_psi_rows_lower (by decide) 43192 rows_43072
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h43584]
  by_cases h44096 : x < 44096
  · have hstart : (43584 : ℝ) ≤ x := by linarith only [h43584]
    have hp : (43598 : ℝ) ≤ Chebyshev.psi 43584 :=
      quarter_psi_rows_lower (by decide) 43598 rows_43584
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h44096]
  by_cases h44608 : x < 44608
  · have hstart : (44096 : ℝ) ≤ x := by linarith only [h44096]
    have hp : (44122 : ℝ) ≤ Chebyshev.psi 44096 :=
      quarter_psi_rows_lower (by decide) 44122 rows_44096
    have hm := Chebyshev.psi_mono hstart
    linarith only [hp, hm, h44608]
  have hstart : (44608 : ℝ) ≤ x := by linarith only [h44608]
  have hp : (44619 : ℝ) ≤ Chebyshev.psi 44608 := quarter_psi_rows_lower (by decide) 44619 rows_44608
  have hm := Chebyshev.psi_mono hstart
  linarith only [hp, hm, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
