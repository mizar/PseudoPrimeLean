/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalHorner16

/-! # Correctness of Horner exponential polynomials -/

public section

namespace PseudoPrime.Analysis

-- Expanding the 16-term polynomial requires a deeper elaboration stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The algebraic identity expands all fixed Taylor coefficients.
private theorem rational_horner_phase_poly (v : ℚ) :
    rationalExpHorner (0, v) 15 0 = rationalPhaseTaylor v 16 := by
  apply Prod.ext <;>
    simp only [rationalExpHorner, rationalPhaseTaylor, rationalComplexAdd, rationalComplexScale,
      rationalComplexMul, rationalComplexPow, Finset.sum_range_succ, Finset.sum_range_zero,
      Prod.fst_add, Prod.snd_add, zero_mul, mul_zero, add_zero, zero_add, sub_zero, zero_sub] <;>
    norm_num only [Nat.factorial] <;>
    ring

-- Expanding the 16-term polynomial requires a deeper elaboration stack.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- The algebraic identity expands all fixed Taylor coefficients.
private theorem rational_horner_real_poly (v : ℚ) :
    rationalExpHorner (v, 0) 15 0 = rationalRealExpTaylor v 16 := by
  apply Prod.ext <;>
    simp only [rationalExpHorner, rationalRealExpTaylor, rationalComplexAdd, rationalComplexScale,
      rationalComplexMul, Finset.sum_range_succ, Finset.sum_range_zero, zero_mul, mul_zero,
      add_zero, zero_add, sub_zero]
  norm_num only [Nat.factorial]
  ring

/-- For every rational phase and every grid and squaring count, the Horner evaluator equals
the existing 16-term rounded phase evaluator. Equality follows from the fixed polynomial
identity before the common rounding and squaring steps. -/
theorem rational_horner_phase_eq (G : ℕ) (v : ℚ) (k : ℕ) :
    rationalHornerPhase16 G v k = rationalScaledPhase G v 16 k := by
  rw [rationalHornerPhase16, rationalScaledPhase, rational_horner_phase_poly]

/-- For every rational exponent and every grid and squaring count, the Horner evaluator
equals the existing 16-term rounded real-exponential evaluator. The common rounded squaring
then preserves the polynomial identity. -/
theorem rational_horner_real_eq (G : ℕ) (v : ℚ) (k : ℕ) :
    rationalHornerRealExp16 G v k = rationalScaledRealExp G v 16 k := by
  rw [rationalHornerRealExp16, rationalScaledRealExp, rational_horner_real_poly]

end PseudoPrime.Analysis
