/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.HighPrecisionLogBounds
public import PseudoPrime.Analysis.IntegerIntervals

/-! # Finite rational witnesses for natural-number logarithms -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Candidate data for a rational logarithm enclosure of a natural-number base. `base` is the
input; `shift` and `depth` select the normalized Taylor computation; `lower` and `upper` are
its proposed rational endpoints. The fields become a valid enclosure only after `check` succeeds.
The witness can be shared by all endpoint heights using the same base. -/
structure NaturalLogWitness where
  base : ℕ
  shift : ℕ
  depth : ℕ
  lower : ℚ
  upper : ℚ

/-- Check the logarithm witness using the internal Taylor bounds and certified `log 2` interval.
The Boolean result includes base positivity, convergence, and both rational endpoint comparisons.
It is consumed by `NaturalLogWitness.sound`. -/
def NaturalLogWitness.check (w : NaturalLogWitness) : Bool :=
  fineLogCheck w.base w.shift w.depth w.lower w.upper

/-- A successful logarithm witness check encloses the real logarithm of its natural base.
The rational checker soundness and the natural-number cast identity prove the claim. -/
theorem NaturalLogWitness.sound (w : NaturalLogWitness) (h : w.check = true) :
    (w.lower : ℝ) ≤ Real.log w.base ∧ Real.log w.base ≤ (w.upper : ℝ) := by
  have h' := fineLogCheck_sound h
  simpa only [Rat.cast_natCast] using h'

/-- Rational bounds for a natural logarithm yield a fixed-point integer interval when the scaled
rational endpoints lie inside its integer endpoints. The scale must be positive. This connects a
shared logarithm witness to phase computations without repeating real-arithmetic proofs. -/
theorem NaturalLogWitness.interval_contains (w : NaturalLogWitness) (G : ℤ) (L : IntegerInterval)
    (hG : 0 < G) (hlog : (w.lower : ℝ) ≤ Real.log w.base ∧ Real.log w.base ≤ (w.upper : ℝ))
    (hl : (L.lower : ℚ) ≤ w.lower * G) (hu : w.upper * G ≤ (L.upper : ℚ)) :
    L.Contains G (Real.log w.base) := by
  have hg : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have hl' : (L.lower : ℝ) ≤ (w.lower : ℝ) * G := by exact_mod_cast hl
  have hu' : (w.upper : ℝ) * G ≤ (L.upper : ℝ) := by exact_mod_cast hu
  constructor
  · exact ((div_le_iff₀ hg).2 hl').trans hlog.1
  · exact hlog.2.trans ((le_div_iff₀ hg).2 hu')

/-- Check all logarithm witnesses in a finite list by recursive traversal. The list is shared
between endpoints and no list value is retrieved by an index. -/
def naturalLogFamilyCheck (data : List NaturalLogWitness) : Bool :=
  data.all NaturalLogWitness.check

/-- Every member of a successfully checked logarithm family bounds the logarithm of its own
base. List membership and the individual soundness theorem establish this without a sortedness
or indexed-lookup assumption. -/
theorem naturalLogFamilyCheck_sound (data : List NaturalLogWitness)
    (h : naturalLogFamilyCheck data = true) {w : NaturalLogWitness} (hw : w ∈ data) :
    (w.lower : ℝ) ≤ Real.log w.base ∧ Real.log w.base ≤ (w.upper : ℝ) := by
  exact w.sound ((List.all_eq_true.mp h) w hw)

end PseudoPrime.Analysis
