/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1510
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrtChecker
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevWalkSound
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Fixed-point psi walk from 1522 to 1539 -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The private starting state encloses the previously certified psi value and
an independently certified logarithm at the common scale `10^12`. -/
private def initial : PsiWalkState :=
  ⟨1522, 7327780000000, 7327781000000, 1516301000000000, 1516996000000000⟩

/-- Every composite entry supplies a coprime-factor witness; prime entries
are checked directly by the execution. This candidate contains no power rows. -/
private def entries : List PsiWalkEntry :=
  [.prime, .composite 4, .composite 25, .composite 2, .composite 3, .composite 8, .composite 11,
    .composite 2, .prime, .composite 4, .composite 3, .composite 2, .composite 5, .composite 512,
    .composite 29, .composite 2, .composite 81]

/-- The candidate final state is checked by executing all entries in order. -/
private def finalState : PsiWalkState :=
  ⟨1539, 7338887595015, 7338892225039, 1530963112671469, 1531658116819066⟩

/-- The kernel verifies the arithmetic checks and the exact state transition. -/
private theorem walk_checked : psiWalk 1000000000000 initial entries = some finalState := by
  decide +kernel

/-- The initial logarithm enclosure and previously certified psi bounds establish
the fixed-point walk invariant at 1522. -/
private theorem initial_valid : PsiWalkValid 1000000000000 initial := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := (1522 : ℚ)) (j := 11) (n := 32) (lo :=
      7327780 / 1000000) (hi := 7327781 / 1000000) (by decide +kernel)
  norm_num only [Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat] at hl
  have hp := psi_1522_bounds
  simp only [PsiWalkValid, initial]
  norm_num only [Nat.cast_ofNat] at ⊢
  constructor
  · decide
  constructor
  · nlinarith only [hl.1]
  constructor
  · nlinarith only [hl.2]
  constructor
  · nlinarith only [hp.1]
  · nlinarith only [hp.2]

/-- The selected entries contain no prime-power payload requiring a separate
logarithm certificate. -/
private theorem entries_valid : entries.Forall (PsiWalkEntryValid 1000000000000) := by
  simp only [entries, List.forall_cons, PsiWalkEntryValid, true_and]
  exact ⟨⟩

/-- The verified walk provides a fixed-point starting invariant at 1539 for
subsequent finite-range certificates, without exporting its execution entries. -/
theorem psi_walk_1539_valid :
    PsiWalkValid 1000000000000
      ⟨1539, 7338887595015, 7338892225039, 1530963112671469, 1531658116819066⟩ := by
  simpa only [finalState] using psi_walk_sound initial_valid entries_valid walk_checked

/-- The fixed-point walk supplies reusable rational psi bounds at 1539. -/
theorem psi_1539_bounds :
    (1530963 : ℝ) / 1000 ≤ Chebyshev.psi ((1539 : ℕ) : ℝ) ∧
      Chebyshev.psi ((1539 : ℕ) : ℝ) ≤ (1531659 : ℝ) / 1000 := by
  have h := psi_walk_sound initial_valid entries_valid walk_checked
  simp only [PsiWalkValid, finalState] at h
  norm_num only [Nat.cast_ofNat] at h
  constructor
  · nlinarith only [h.2.2.2.1]
  · nlinarith only [h.2.2.2.2]

/-- The unconditional psi error is at most four fifths of the square root on
`[1522, 1540)`. A sequential fixed-point walk supplies its endpoint bound and
its arithmetic certificate is kept private. -/
theorem psi_four_fifths_1522_1540 {x : ℝ} (ha : 1522 ≤ x) (hb : x < 1540) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have hc : psiSqrtCellCheck ⟨1522, 1540, 1516301, 1531659, 31100, 31300⟩ = true := by
    decide +kernel
  exact
    psi_sqrt_cell_sound ⟨1522, 1540, 1516301, 1531659, 31100, 31300⟩ hc psi_1522_bounds.1
      psi_1539_bounds.2 ha hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
