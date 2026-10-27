/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.EulerMascheroniBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Midpoint harmonic bounds for the Euler constant -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For nonnegative x, the midpoint logarithmic increment dominates 1/(x+1).
The rational lower bound for log(1+u) proves the inequality. This is the
one-step estimate for the decreasing midpoint harmonic sequence. -/
theorem midpoint_log_increment {x : ℝ} (hx : 0 ≤ x) :
    (x + 1)⁻¹ ≤ Real.log (x + 3 / 2) - Real.log (x + 1 / 2) := by
  have ha : 0 < x + 1 / 2 := by linarith only [hx]
  have hb : 0 < x + 1 := by linarith only [hx]
  have h := Real.le_log_one_add_of_nonneg (inv_nonneg.mpr ha.le)
  have he : 2 * (x + 1 / 2)⁻¹ / ((x + 1 / 2)⁻¹ + 2) = (x + 1)⁻¹ := by
    field_simp [ha.ne', hb.ne']
    ring
  have hl : 1 + (x + 1 / 2)⁻¹ = (x + 3 / 2) / (x + 1 / 2) := by
    field_simp [ha.ne', hb.ne']
    ring
  rw [he, hl, Real.log_div (by linarith only [hx]) ha.ne'] at h
  exact h

/-- The shifted midpoint approximation H_(n+1)-log(n+3/2).
Its natural input starts at zero; every logarithm argument is positive.
The sequence gives rapidly convergent upper bounds for the Euler constant. -/
noncomputable def midpointEulerSequence (n : ℕ) : ℝ :=
  (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 3 / 2)

/-- The midpoint harmonic sequence decreases on all natural inputs.
Expand one harmonic increment and apply the midpoint logarithmic bound.
This monotonicity will turn its limit into pointwise upper estimates. -/
theorem midpointEulerSequence_antitone : Antitone midpointEulerSequence := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  have h :=
    midpoint_log_increment (x := (n : ℝ) + 1)
      (by exact add_nonneg (Nat.cast_nonneg n) (by norm_num only))
  change
    (harmonic (n + 1 + 1) : ℝ) - Real.log (↑(n + 1) + 3 / 2) ≤
      (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 3 / 2)
  rw [harmonic_succ (n + 1), Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  norm_num only [Nat.cast_add, Nat.cast_one] at *
  have he : (n : ℝ) + 1 + 1 / 2 = n + 3 / 2 := by ring
  rw [he] at h
  linarith only [h]

/-- The midpoint harmonic sequence tends to the Euler constant.
Squeeze it between the two classical harmonic approximations.
This identifies the limit without an additional asymptotic error estimate. -/
theorem midpointEulerSequence_tendsto :
    Filter.Tendsto midpointEulerSequence Filter.atTop (nhds Real.eulerMascheroniConstant) := by
  apply
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      (Real.tendsto_harmonic_sub_log_add_one.comp (Filter.tendsto_add_atTop_nat 1))
      (Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1))
  · intro n
    have h :=
      Real.log_le_log (by linarith only [Nat.cast_nonneg (α := ℝ) n] : (0 : ℝ) < n + 3 / 2)
        (by
          simp only [Nat.cast_add, Nat.cast_one]; linarith only : (n : ℝ) + 3 / 2 ≤ ↑(n + 1) + 1)
    exact sub_le_sub_left h _
  · intro n
    have h :=
      Real.log_le_log (by exact_mod_cast Nat.succ_pos n : (0 : ℝ) < ↑(n + 1))
        (by
          simp only [Nat.cast_add, Nat.cast_one]; linarith only : (↑(n + 1) : ℝ) ≤ n + 3 / 2)
    exact sub_le_sub_left h _

/-- Every midpoint approximation is an upper bound for the Euler constant.
Apply antitonicity and the established limit. The result permits short
rational certificates at any positive harmonic index. -/
theorem eulerMascheroniConstant_le_midpoint (n : ℕ) :
    Real.eulerMascheroniConstant ≤ midpointEulerSequence n := by
  exact midpointEulerSequence_antitone.le_of_tendsto midpointEulerSequence_tendsto n

/-- The Euler constant is at most 5773/10000.
Use H_32 and a six-term rational logarithm certificate at 65/2.
This precision is sufficient for the improved LLS correction constants. -/
theorem eulerMascheroniConstant_le_5773_div_10000 :
    Real.eulerMascheroniConstant ≤ (5773 / 10000 : ℝ) := by
  have hh : harmonic 32 = (586061125622639 / 144403552893600 : ℚ) := by
    norm_num only [harmonic, Finset.sum_range_succ]
  have hc : rationalLogIntervalCheck (65 / 2) 5 6 (348124 / 100000) (348125 / 100000) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have hg := eulerMascheroniConstant_le_midpoint 31
  norm_num only [midpointEulerSequence, hh, Rat.cast_div, Rat.cast_ofNat, Nat.reduceAdd,
    Nat.cast_ofNat] at hg
  linarith only [hl, hg]

end PseudoPrime.Analysis
