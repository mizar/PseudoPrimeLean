/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalSqrt
public import PseudoPrime.Analysis.IntegerIntervals
public import PseudoPrime.Analysis.IntegerIntervalComputed

/-! # Checked intervals for reciprocal square roots -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A checked square-root interval followed by a checked reciprocal interval encloses the
reciprocal square root of every real input in the original interval. Both checks enforce their
own scale and positivity conditions. This combines reusable integer checks for amplitudes of
critical-line complex powers. -/
theorem reciprocal_sqrt_contains {G : ℤ} {N S A : IntegerInterval} {x : ℝ} (hn : N.Contains G x)
    (hs : integerSqrtCheck G N.lower N.upper S.lower S.upper = true)
    (ha : integerReciprocalCheck G S.lower S.upper A.lower A.upper = true) :
    A.Contains G (Real.sqrt x)⁻¹ := by
  exact integerReciprocalCheck_sound ha (integerSqrtCheck_sound hs hn)

/-- Candidate intervals for the square root and its reciprocal at a shared integer scale.
The `sqrt` field bounds the square root and `inverse` bounds its reciprocal; these properties
are established only when `check` succeeds. The witness is independent of endpoint height and
can therefore be shared across all phase certificates for the same integer base. -/
structure AmplitudeWitness where
  sqrt : IntegerInterval
  inverse : IntegerInterval

/-- Check the square-root and reciprocal intervals for a natural-number base at scale `G`.
The base interval is computed internally and both existing integer checks must succeed. The
Boolean result is consumed by `AmplitudeWitness.sound`, not assumed by final numerical theorems. -/
def AmplitudeWitness.check (w : AmplitudeWitness) (G : ℤ) (n : ℕ) : Bool :=
  let N := roundedConstant G n 1
  integerSqrtCheck G N.lower N.upper w.sqrt.lower w.sqrt.upper &&
    integerReciprocalCheck G w.sqrt.lower w.sqrt.upper w.inverse.lower w.inverse.upper

/-- At positive scale, a successful amplitude witness check encloses `1 / √n`.
The rounded base constant and the checked square-root and reciprocal bounds are composed.
This provides the reusable amplitude input to the compact critical-power term checker. -/
theorem AmplitudeWitness.sound (w : AmplitudeWitness) (G : ℤ) (n : ℕ) (hG : 0 < G)
    (h : w.check G n = true) : w.inverse.Contains G (Real.sqrt n)⁻¹ := by
  have hc := Bool.and_eq_true_iff.mp h
  have hn := roundedConstant_contains (G := G) (p := n) (d := 1) hG (by decide)
  have hn' : (roundedConstant G n 1).Contains G (n : ℝ) := by
    simpa only [Int.cast_natCast, Int.cast_one, div_one] using hn
  exact reciprocal_sqrt_contains hn' hc.1 hc.2

/-- Check a finite collection of natural bases paired with amplitude witnesses at a common scale.
The list is traversed by `List.all`; no value is retrieved by list index. Successful checks can
be reused for both endpoints of every selected zero interval. -/
def amplitudeFamilyCheck (G : ℤ) (data : List (ℕ × AmplitudeWitness)) : Bool :=
  data.all (fun entry ↦ entry.2.check G entry.1)

/-- A successful finite amplitude-family check certifies the reciprocal square root associated
with every member of the input list. Membership and `AmplitudeWitness.sound` give the result
without assuming that the list is sorted or that any indexed lookup is valid. -/
theorem amplitudeFamilyCheck_sound (G : ℤ) (hG : 0 < G) (data : List (ℕ × AmplitudeWitness))
    (h : amplitudeFamilyCheck G data = true) {n : ℕ} {w : AmplitudeWitness} (hw : (n, w) ∈ data) :
    w.inverse.Contains G (Real.sqrt n)⁻¹ := by
  exact w.sound G n hG ((List.all_eq_true.mp h) (n, w) hw)

end PseudoPrime.Analysis
