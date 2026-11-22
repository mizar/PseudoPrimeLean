/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.IntegerIntervalPhase

/-! # Checked rational Taylor coordinates for phase centers -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Check the small-angle domain and the exact 25-term rational Taylor
coordinates against scaled integer intervals. The existing rational phase
evaluator is used unchanged; all comparisons are executable rational arithmetic. -/
def rationalPhaseTaylorCheck (q : ℚ) (R I : IntegerInterval) (G : ℤ) : Bool :=
  let z := rationalPhaseTaylor q 25
  decide
    (-(1 / 4 : ℚ) ≤ q ∧
      q ≤ 1 / 4 ∧
      0 < G ∧
      (R.lower : ℚ) / G ≤ z.1 ∧
      z.1 ≤ (R.upper : ℚ) / G ∧ (I.lower : ℚ) / G ≤ z.2 ∧ z.2 ≤ (I.upper : ℚ) / G)

/-- Successful rational checking encloses the actual complex Taylor
polynomial. The existing finite-series cast theorem identifies the rational
evaluator, and the four rational inequalities transfer to real coordinates. -/
theorem rationalPhaseTaylorCheck_sound {q : ℚ} {R I : IntegerInterval} {G : ℤ}
    (h : rationalPhaseTaylorCheck q R I G = true) :
    complexIntervalContains R I G
      (∑ m ∈ Finset.range 25, (Complex.I * (q : ℂ)) ^ m / (m.factorial : ℂ)) := by
  have hc := of_decide_eq_true h
  have hr : R.Contains G ((rationalPhaseTaylor q 25).1 : ℝ) := by
    constructor
    · exact_mod_cast hc.2.2.2.1
    · exact_mod_cast hc.2.2.2.2.1
  have hi : I.Contains G ((rationalPhaseTaylor q 25).2 : ℝ) := by
    constructor
    · exact_mod_cast hc.2.2.2.2.2.1
    · exact_mod_cast hc.2.2.2.2.2.2
  rw [← rationalPhaseTaylor_cast]
  exact ⟨hr, hi⟩

/-- A checked rational Taylor enclosure, widened by the proved analytic
error, contains the true small-angle phase. This discharges the polynomial
value hypothesis required by the existing phase transport theorem. -/
theorem rational_phase_taylor_contains {q : ℚ} {R I : IntegerInterval} {G r : ℤ}
    (h : rationalPhaseTaylorCheck q R I G = true) (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G) :
    complexIntervalContains (R.widen r) (I.widen r) G (Complex.exp ((q : ℂ) * Complex.I)) := by
  have hc := of_decide_eq_true h
  have hd : |(q : ℝ)| ≤ 1 / 4 := by
    apply abs_le.mpr
    constructor
    · have hh : ((-(1 / 4 : ℚ) : ℚ) : ℝ) ≤ (q : ℝ) := Rat.cast_le.mpr hc.1
      norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
      exact hh
    · have hh : (q : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) := Rat.cast_le.mpr hc.2.1
      norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
      exact hh
  have hp := rationalPhaseTaylorCheck_sound h
  have ht :
    complexIntervalContains R I G
      (∑ m ∈ Finset.range 25, (((q : ℝ) : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) := by
    simpa only [Complex.ofReal_ratCast, mul_comm] using hp
  simpa only [Complex.ofReal_ratCast] using phase_taylor24_contains hd ht hr

/-- A rational Taylor certificate followed by a recursively checked
doubling chain encloses the true full phase. The supplied length identifies
the exact power of two; no arithmetic expression equality remains unproved. -/
theorem rational_phase_chain_contains (chain : List PhaseSquareWitness) (n : ℕ) {q : ℚ}
    {R I : IntegerInterval} {G r : ℤ} (hlen : chain.length = n)
    (h : rationalPhaseTaylorCheck q R I G = true) (hr : (1 / 2 ^ 120 : ℝ) ≤ (r : ℝ) / G)
    (hc : phaseSquareCheck G (R.widen r) (I.widen r) chain = true) :
    complexIntervalContains (phaseSquareResult (R.widen r) (I.widen r) chain).1
      (phaseSquareResult (R.widen r) (I.widen r) chain).2 G
      (Complex.exp ((((2 : ℝ) ^ n * (q : ℝ) : ℝ) : ℂ) * Complex.I)) := by
  have ht := rational_phase_taylor_contains h hr
  have hp :
    complexIntervalContains (R.widen r) (I.widen r) G
      (Complex.exp (((q : ℝ) : ℂ) * Complex.I)) := by
    simpa only [Complex.ofReal_ratCast] using ht
  have he := phaseSquareCheck_sound chain G (R.widen r) (I.widen r) (q : ℝ) hc hp
  rw [hlen] at he
  exact he

end PseudoPrime.Analysis
