/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.HighFactorialEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.HighVariableComparison

/-! # Strict comparison of factorial and paired envelopes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For `U ≥ 22`, the factorial radius coefficient is strictly below the paired coefficient.
Positive denominators permit an exact rational cross-multiplication. -/
theorem factorialAlpha_lt_paired {U : ℝ} (hU : 22 ≤ U) : factorialAlpha U < pairedAlpha U := by
  have hf : 0 < (3 / 2 : ℝ) * U + 49 / 50 := by linarith only [hU]
  have hp : 0 < (3 / 2 : ℝ) * U + 339 / 500 := by linarith only [hU]
  dsimp only [factorialAlpha, pairedAlpha]
  apply (div_lt_div_iff₀ hf hp).mpr
  nlinarith only [hU]

/-- On `80000 ≤ log n ≤ 100000`, the factorial-selected cutoff is strictly smaller than the
paired cutoff. The paired bound is the active preceding minimum, and its coefficient is
strictly larger than the factorial coefficient. -/
theorem factorialSelected_lt_paired {n : ℕ} (hL : (80000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 100000) : factorialSelected n < pairedSelected n := by
  have h70 : (70000 : ℝ) ≤ Real.log n := by linarith only [hL]
  have hold := pairedSelected_lt_previous h70 hU
  have hpold : pairedWitnessBound n < highWindowExtended n := by
    rw [pairedSelected, ite_eq_left h70] at hold
    exact (min_lt_iff.mp hold).resolve_left (lt_irrefl _)
  have hpair : pairedSelected n = pairedWitnessBound n := by
    rw [pairedSelected, ite_eq_left h70, min_eq_right hpold.le]
  have hU0 := high_log_twice_ge_22 h70
  have ha0 := (factorialAlpha_bounds hU0).1
  have halt := factorialAlpha_lt_paired hU0
  have hsquare :
    (factorialAlpha (2 * Real.log (Real.log n))) ^ 2 <
      (pairedAlpha (2 * Real.log (Real.log n))) ^ 2 :=
    (sq_lt_sq₀ (by linarith only [ha0]) (by linarith only [ha0, halt])).mpr halt
  have hLsq : 0 < Real.log n ^ 2 := sq_pos_of_pos (by linarith only [hL])
  have hnew : factorialSelected n ≤ factorialWitnessBound n := by
    rw [factorialSelected, ite_eq_left hL]
    exact min_le_right _ _
  rw [hpair]
  have hlt := mul_lt_mul_of_pos_right hsquare hLsq
  exact hnew.trans_lt hlt

end PseudoPrime.PrimeTestBounds.MillerRabin
