/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalHorner

/-! # Linear witness checks for integer interval Horner phases -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Integer interval data for one Horner step: a rational factor and both output coordinates.
The checker enforces the constant and two product constraints; lists compose the steps. -/
structure PhaseHornerWitness where
  factor : IntegerInterval
  real : IntegerInterval
  imag : IntegerInterval

/-- Return the first certified output, or the exact depth-zero coordinates for an empty list.
Pattern matching avoids indexing the witness list. -/
def phaseHornerResult (G : ℤ) : List PhaseHornerWitness → IntegerInterval × IntegerInterval
  | [] => (⟨G, G⟩, ⟨0, 0⟩)
  | w :: _ => (w.real, w.imag)

/-- Check a Horner witness list at the supplied denominator offset.
Three integer checks validate each step against the next list element or the exact base case. -/
def phaseHornerCheck (G p d : ℤ) : ℕ → List PhaseHornerWitness → Bool
  | _, [] => true
  | j, w :: rest =>
    let v := phaseHornerResult G rest
    integerConstantCheck G p (d * ((j : ℤ) + 1)) w.factor.lower w.factor.upper &&
      integerProductCheck G w.factor.lower w.factor.upper v.2.lower v.2.upper (G - w.real.upper)
        (G - w.real.lower) &&
      integerProductCheck G w.factor.lower w.factor.upper v.1.lower v.1.upper w.imag.lower
        w.imag.upper &&
      phaseHornerCheck G p d (j + 1) rest

/-- At positive scale, a successful witness list encloses the real Horner polynomial.
Induction composes checked steps, with depth equal to the list length. -/
theorem phaseHornerCheck_sound (G p d : ℤ) (chain : List PhaseHornerWitness) (j : ℕ) (hg : 0 < G)
    (h : phaseHornerCheck G p d j chain = true) :
    (phaseHornerResult G chain).1.Contains G (realPhaseHorner ((p : ℝ) / d) chain.length j).1 ∧
      (phaseHornerResult G chain).2.Contains G
        (realPhaseHorner ((p : ℝ) / d) chain.length j).2 := by
  induction chain generalizing j with
  | nil =>
    have hr : (0 : ℝ) < G := (Int.cast_pos (R := ℝ)).mpr hg
    constructor <;> constructor <;>
      simp only [phaseHornerResult, List.length_nil, realPhaseHorner, Int.cast_zero, zero_div,
        div_self (ne_of_gt hr), le_refl]
  | cons w rest ih =>
    have hc := Bool.and_eq_true_iff.mp h
    have hp := Bool.and_eq_true_iff.mp hc.1
    have hq := Bool.and_eq_true_iff.mp hp.1
    have hv := ih (j + 1) hc.2
    exact hornerStep_real rest.length j hg hq.1 hv hq.2 hp.2

end PseudoPrime.Analysis
