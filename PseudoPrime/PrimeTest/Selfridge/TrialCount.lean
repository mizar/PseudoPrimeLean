/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Selfridge.Nonempty

/-!
# Discrete classical Selfridge trial counts
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

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
theorem classicalTrialCountThrough_eq_sub_three_div_two {i : ℕ} (hi : isClassicalCandidate i) :
    classicalTrialCountThrough i = (i - 3) / 2 := by
  obtain ⟨h5, k, hk⟩ := hi
  unfold classicalTrialCountThrough
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h5
  rw [Nat.add_sub_cancel_left, Nat.sub_add_comm (by decide : 3 ≤ 5)]
  norm_num only
  rw [Nat.add_comm 2 t, Nat.add_div_right t (by decide : 0 < 2)]

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
    (h : (FirstStopNeOneSet isClassicalCandidate n).Nonempty) : ℕ :=
  classicalTrialCountThrough (firstStopNeOne isClassicalCandidate n h)

/-- Given `n` and nonemptiness of its classical pure `-1` stopping set, apply
`classicalTrialCountThrough` to the first stopping value. This is the pointwise trial count
corresponding to `classicalNegOneTrialMaximum`. -/
noncomputable def classicalNegOneTrialCount (n : ℕ)
    (h : (FirstStopNegOneSet isClassicalCandidate n).Nonempty) : ℕ :=
  classicalTrialCountThrough (firstStopNegOne isClassicalCandidate n h)

end PseudoPrime.PrimeTest
