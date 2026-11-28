/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ComputedPhaseRotation
public import PseudoPrime.Analysis.IntegerIntervalPhaseCells

/-! # Computed Taylor, angle doubling, and linear phase propagation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Round the rational coordinates of the small-angle Taylor polynomial, then
add one tick for the truncation error. -/
def computedPhaseTaylor (G : ℤ) (q : ℚ) : IntegerInterval × IntegerInterval :=
  let z := rationalPhaseTaylor q 25
  ((roundedConstant G z.1.num z.1.den).widen 1, (roundedConstant G z.2.num z.2.den).widen 1)

/-- At scales where one tick dominates the Taylor remainder, the computed
rectangle contains the small-angle phase. -/
theorem computed_phase_taylor_contains {G : ℤ} {q : ℚ} (hg : 0 < G) (hq : |(q : ℝ)| ≤ 1 / 4)
    (he : (1 / 2 ^ 120 : ℝ) ≤ 1 / (G : ℝ)) :
    complexIntervalContains (computedPhaseTaylor G q).1 (computedPhaseTaylor G q).2 G
      (Complex.exp (((q : ℝ) : ℂ) * Complex.I)) := by
  have h (a : ℚ) : (roundedConstant G a.num a.den).Contains G (a : ℝ) := by
    rw [Rat.cast_def]
    have hd : (0 : ℤ) < a.den := by exact_mod_cast a.den_pos
    simpa only [Int.cast_natCast] using roundedConstant_contains (p := a.num) hg hd
  apply phase_taylor24_contains hq _ (by simpa only [Int.cast_one] using he)
  have ht :
    complexIntervalContains
      (roundedConstant G (rationalPhaseTaylor q 25).1.num (rationalPhaseTaylor q 25).1.den)
      (roundedConstant G (rationalPhaseTaylor q 25).2.num (rationalPhaseTaylor q 25).2.den) G
      (∑ m ∈ Finset.range 25, (Complex.I * (q : ℂ)) ^ m / (m.factorial : ℂ)) := by
    rw [← rationalPhaseTaylor_cast]
    exact ⟨h _, h _⟩
  simpa only [Complex.ofReal_ratCast, mul_comm] using ht

/-- Repeated outward-rounded doubling evaluates the phase of the scaled angle
from a single small-angle Taylor enclosure. -/
def computedPhaseDouble (G : ℤ) (q : ℚ) : ℕ → IntegerInterval × IntegerInterval
  | 0 => computedPhaseTaylor G q
  | n + 1 =>
      let z := computedPhaseDouble G q n
      roundedPhaseDouble G z.1 z.2

/-- Repeated doubling multiplies the angle by the corresponding power of two. -/
theorem computed_phase_double_contains {G : ℤ} {q : ℚ} (hg : 0 < G) (hq : |(q : ℝ)| ≤ 1 / 4)
    (he : (1 / 2 ^ 120 : ℝ) ≤ 1 / (G : ℝ)) (n : ℕ) :
    complexIntervalContains (computedPhaseDouble G q n).1 (computedPhaseDouble G q n).2 G
      (Complex.exp ((((2 : ℝ) ^ n * (q : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  induction n with
  | zero =>
    simpa only [computedPhaseDouble, pow_zero, one_mul] using
      computed_phase_taylor_contains hg hq he
  | succ n ih =>
    have h := rounded_phase_double_contains hg ih
    rw [← two_mul, ← mul_assoc, ← pow_succ' (2 : ℝ)] at h
    exact h

/-- Compute the linearized phase enclosure from a center rectangle and a
displacement interval, widening by an integer quadratic-error cap. -/
def computedPhaseCell (G : ℤ) (Q : IntegerInterval × IntegerInterval) (D : IntegerInterval)
    (error : ℤ) : IntegerInterval × IntegerInterval :=
  let sd := roundedProduct G Q.2 D
  let cd := roundedProduct G Q.1 D
  ((Q.1.add sd.neg).widen error, (Q.2.add cd).widen error)

/-- Positive scale lets the computed products discharge the two product
checks in the linear phase transport. -/
theorem computed_phase_cell_contains {G error : ℤ} {Q : IntegerInterval × IntegerInterval}
    {D : IntegerInterval} {c x : ℝ} (hg : 0 < G)
    (hc : complexIntervalContains Q.1 Q.2 G (Complex.exp ((c : ℂ) * Complex.I)))
    (hd : D.Contains G (x - c)) (he : (x - c) ^ 2 / 2 ≤ (error : ℝ) / G) :
    complexIntervalContains (computedPhaseCell G Q D error).1 (computedPhaseCell G Q D error).2 G
      (Complex.exp ((x : ℂ) * Complex.I)) := by
  exact
    phase_cell_contains hc hd (roundedProduct_check G Q.2 D hg) (roundedProduct_check G Q.1 D hg) he

end PseudoPrime.Analysis
