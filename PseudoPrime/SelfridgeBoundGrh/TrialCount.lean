/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.SelfridgeBoundGrh.MaximumBridge
import PseudoPrime.PseudoSquare.Bounds.ElementaryOmegaFinal

/-!
# Trial counts for the classical Selfridge scan

`classicalNeOneMaximum` / `classicalNegOneMaximum` (in `MaximumBridge`) report the largest
stopping *value* `i = |D|` reached by the classical scan, not the number of Jacobi-symbol trials
taken to reach it. Since the classical candidate sequence enumerates every odd integer from `5`
upward, the trial count for a stop at `i` is `(i - 3) / 2`. This file formalizes that value/count
correspondence and transports the public elementary bounds
(`classicalMaximum_elementary_bound_explicit`) into a worst-case trial-count bound.
-/

namespace PseudoPrime.SelfridgeBoundGrh

/-- The zero-indexed classical candidate `2*k + 5`, enumerating `5, 7, 9, 11, …`.
This records the value/index convention used by `classicalTrialCountThrough`. -/
def classicalCandidateAt (k : ℕ) : ℕ :=
  2 * k + 5

/-- The natural-number expression `(i - 5)/2 + 1`.
For a classical candidate `i`, this counts the candidates from `5` through `i`, inclusive.
It converts stopping-value bounds into trial-count bounds. Outside the candidate range it is
still defined using natural subtraction and division; in particular it equals `1` for `i < 5`. -/
def classicalTrialCountThrough (i : ℕ) : ℕ :=
  (i - 5) / 2 + 1

/-- For a classical candidate `i` (odd and at least `5`), the trial count equals `(i-3)/2`.
Unfolding the count and using the candidate conditions gives this alternative closed form. -/
theorem classicalTrialCountThrough_eq_sub_three_div_two {i : ℕ}
    (hi : PrimeTest.isClassicalCandidate i) :
    classicalTrialCountThrough i = (i - 3) / 2 := by
  obtain ⟨h5, k, hk⟩ := hi
  unfold classicalTrialCountThrough
  omega

/-- If `a ≤ b`, then `classicalTrialCountThrough a ≤ classicalTrialCountThrough b`.
Monotonicity of natural subtraction and division proves this for all naturals, allowing
stopping-value comparisons to be transported to counts. -/
theorem classicalTrialCountThrough_mono {a b : ℕ} (hab : a ≤ b) :
    classicalTrialCountThrough a ≤ classicalTrialCountThrough b := by
  unfold classicalTrialCountThrough
  have hsub : a - 5 ≤ b - 5 := Nat.sub_le_sub_right hab 5
  exact Nat.add_le_add_right (Nat.div_le_div_right hsub) 1

/-- Given `n` and nonemptiness of its classical `≠1` stopping set, apply
`classicalTrialCountThrough` to the first stopping value. This is the pointwise trial count
corresponding to `classicalNeOneTrialMaximum`. -/
noncomputable def classicalNeOneTrialCount (n : ℕ)
    (h :
      (PrimeTest.FirstStopNeOneSet PrimeTest.isClassicalCandidate
          n).Nonempty) :
    ℕ :=
  classicalTrialCountThrough
    (PrimeTest.firstStopNeOne PrimeTest.isClassicalCandidate n h)

/-- Given `n` and nonemptiness of its classical pure `-1` stopping set, apply
`classicalTrialCountThrough` to the first stopping value. This is the pointwise trial count
corresponding to `classicalNegOneTrialMaximum`. -/
noncomputable def classicalNegOneTrialCount (n : ℕ)
    (h :
      (PrimeTest.FirstStopNegOneSet PrimeTest.isClassicalCandidate
          n).Nonempty) :
    ℕ :=
  classicalTrialCountThrough
    (PrimeTest.firstStopNegOne PrimeTest.isClassicalCandidate n h)

/-- Apply `classicalTrialCountThrough` to the largest classical `≠1` stopping value up to `B`.
This is the aggregate count used in `classicalTrialMaximum_elementary_bound_explicit`.
If the admissible input set is empty, its stopping-value supremum is `0` and this definition
returns `1`, by the convention in `classicalTrialCountThrough`. -/
noncomputable def classicalNeOneTrialMaximum (B : ℕ) : ℕ :=
  classicalTrialCountThrough (classicalNeOneMaximum B)

/-- Apply `classicalTrialCountThrough` to the largest classical pure `-1` stopping value up to `B`.
This is the aggregate count bounded by `classicalNegOneTrialMaximum_real_le`.
If the admissible input set is empty, its stopping-value supremum is `0` and this definition
returns `1`, by the convention in `classicalTrialCountThrough`. -/
noncomputable def classicalNegOneTrialMaximum (B : ℕ) : ℕ :=
  classicalTrialCountThrough (classicalNegOneMaximum B)

/-- For every natural `i`, the real trial count is at most `i/2 + 1`.
The proof uses `↑((i-5)/2) ≤ ↑(i-5)/2` from `Nat.cast_div_le` and
`↑(i-5) ≤ ↑i` from `Nat.sub_le`. This supplies the count estimate used by
`classicalNegOneTrialMaximum_real_le`; no candidate assumption is needed. -/
theorem classicalTrialCountThrough_real_le (i : ℕ) :
    (classicalTrialCountThrough i : ℝ) ≤ (i : ℝ) / 2 + 1 := by
  unfold classicalTrialCountThrough
  have hdiv : (((i - 5) / 2 : ℕ) : ℝ) ≤ ((i - 5 : ℕ) : ℝ) / 2 := Nat.cast_div_le
  have hsub : ((i - 5 : ℕ) : ℝ) ≤ (i : ℝ) := by exact Nat.cast_le.mpr (Nat.sub_le i 5)
  push_cast
  linarith only [hdiv, hsub]

/-- Under GRH and `B ≥ 751`, the pure `-1` aggregate trial count is at most
`elementaryRadius B / 2 + 1`. Rewrite the stopping-value maximum as `QNegOne B` using
`classicalNegOneMaximum_eq_QNegOne_of_399_le`, apply `elementary_formula_real`, then apply
`classicalTrialCountThrough_real_le`. This is the real bound used by the explicit count theorem. -/
theorem classicalNegOneTrialMaximum_real_le
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ}
    (hB : 751 ≤ B) :
    (classicalNegOneTrialMaximum B : ℝ) ≤ PseudoSquare.elementaryRadius B / 2 + 1 := by
  have hM : (classicalNegOneMaximum B : ℝ) ≤ PseudoSquare.elementaryRadius B := by
    have h399 : 399 ≤ B := by omega
    rw [classicalNegOneMaximum_eq_QNegOne_of_399_le h399]
    exact (PseudoSquare.elementary_formula_real hGRH (by omega)).2
  unfold classicalNegOneTrialMaximum
  have hbase := classicalTrialCountThrough_real_le (classicalNegOneMaximum B)
  linarith only [hbase, hM]

/-- Under GRH and `B ≥ 751`, the classical `≠1` aggregate trial count is at most the pure
`-1` aggregate count, and the latter is at most
`(log(4B) + (24/5)*loglog(4B) + 3)² / 2 + 1` as a real number.
Count monotonicity transports the stopping-value comparison; unfolding `elementaryRadius`
in `classicalNegOneTrialMaximum_real_le` gives the explicit upper bound. -/
theorem classicalTrialMaximum_elementary_bound_explicit
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {B : ℕ}
    (hB : 751 ≤ B) :
    classicalNeOneTrialMaximum B ≤ classicalNegOneTrialMaximum B ∧
      (classicalNegOneTrialMaximum B : ℝ) ≤
        (Real.log (4 * (B : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (B : ℝ))) + 3) ^ 2 / 2 +
          1 := by
  refine ⟨?_, ?_⟩
  · exact classicalTrialCountThrough_mono (classicalNeOneMaximum_le_classicalNegOneMaximum B)
  · have := classicalNegOneTrialMaximum_real_le hGRH hB
    simpa only [PseudoSquare.elementaryRadius] using this

end PseudoPrime.SelfridgeBoundGrh
