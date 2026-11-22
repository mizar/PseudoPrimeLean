/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.PsiSqrtBound.ChebyshevSqrt1423
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtChecker
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimePowerWitnessPrefix

/-! # Incremental square-root psi certificate from 1510 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Coprime-factor witnesses for the non-prime-powers in `(1510, 1522]`;
the zero entry marks the single prime-power row checked separately. -/
private def witnesses : List ℕ :=
  [0, 8, 17, 2, 3, 4, 37, 2, 49, 16, 9, 2]

/-- The prime-power logarithm row supplies certified bounds for the increment. -/
private def rows : List PrimePowerLogRow :=
  [⟨1511, 0, 11, 32, 7320 / 1000, 7321 / 1000⟩]

/-- Kernel arithmetic validates each non-prime-power witness. -/
private theorem witnesses_checked : primePowerWitnessScan 1511 witnesses = true := by decide +kernel

/-- Kernel arithmetic checks the prime base and its logarithm interval. -/
private theorem rows_checked : rows.all primePowerLogCheck = true := by decide +kernel

/-- The marked events agree with the checked prime-power logarithm rows. -/
private theorem events_checked :
    primePowerWitnessEvents 1511 witnesses = rows.map (fun r ↦ r.p ^ (r.k + 1)) := by decide +kernel

/-- The sequential interval increment extends the seed bounds to 1522.
The numerical bounds can be reused as a seed without exposing the certificates. -/
theorem psi_1522_bounds :
    (1516301 : ℝ) / 1000 ≤ Chebyshev.psi ((1522 : ℕ) : ℝ) ∧
      Chebyshev.psi ((1522 : ℕ) : ℝ) ≤ (1516996 : ℝ) / 1000 := by
  have h :=
    psi_prefix_bounds_of_witnesses psi_1510_bounds.1 psi_1510_bounds.2 witnesses rows
      witnesses_checked rows_checked events_checked
  norm_num only [witnesses, rows, List.length_cons, List.length_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_one, Nat.reduceAdd] at h
  constructor
  · linarith only [h.1]
  · linarith only [h.2]

/-- The unconditional psi error is at most four fifths of the square root on
`[1510, 1523)`. The endpoint increment is certified from the prior seed using
one sequential witness stream and one prime logarithm row. -/
theorem psi_four_fifths_1510_1523 {x : ℝ} (ha : 1510 ≤ x) (hb : x < 1523) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have hc : psiSqrtCellCheck ⟨1510, 1523, 1508981, 1516996, 31000, 31000⟩ = true := by
    decide +kernel
  exact
    psi_sqrt_cell_sound ⟨1510, 1523, 1508981, 1516996, 31000, 31000⟩ hc psi_1510_bounds.1
      psi_1522_bounds.2 ha hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
