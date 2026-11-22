/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-! # Exact quarter-turn decomposition of a complex phase -/

public section

namespace PseudoPrime.Analysis

/-- Integer powers of the imaginary unit depend only on the exponent modulo four, including for
negative exponents. Applying the periodicity theorem to the unit represented by `I` proves the
identity. This lets the phase checker select one of four exact coordinate rotations. -/
theorem I_zpow_mod_four (k : ℤ) : Complex.I ^ k = Complex.I ^ (k % 4) := by
  let u : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero
  have hu : u ^ 4 = 1 := by
    apply Units.ext
    simpa only [Units.val_pow_eq_pow_val, Units.val_one, u, Units.val_mk0] using Complex.I_pow_four
  have h := zpow_eq_zpow_emod' k hu
  have hv := congrArg (fun v : ℂˣ ↦ (v : ℂ)) h
  simpa only [Units.val_zpow_eq_zpow_val, u, Units.val_mk0, Nat.cast_ofNat] using hv

/-- Splitting a real phase into a remainder and an integer multiple of `π / 2` factors its
complex exponential into the remainder phase and an integer power of `I`. The integer may be
negative. The proof uses the exact value of the quarter-turn exponential, so interval bounds on
the remainder can be transported without replacing the true value of `π` by an approximation. -/
theorem exp_quarter_turn (r : ℝ) (k : ℤ) :
    Complex.exp (((r + k * (Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((r : ℂ) * Complex.I) * Complex.I ^ k := by
  have h :
    (((r + k * (Real.pi / 2) : ℝ) : ℂ) * Complex.I) =
      (r : ℂ) * Complex.I + (k : ℂ) * ((Real.pi : ℂ) / 2 * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_div_two_mul_I]

/-- The exponential of a real phase equals two successive squares of the phase at one quarter
of the argument. The exponential multiplication law proves this exact identity. A certified
small phase can therefore be transported to the full reduced phase with two interval squares. -/
theorem exp_phase_two_squares (r : ℝ) :
    Complex.exp ((r : ℂ) * Complex.I) = (Complex.exp (((r / 4 : ℝ) : ℂ) * Complex.I) ^ 2) ^ 2 := by
  have h : (r : ℂ) * Complex.I = (4 : ℂ) * (((r / 4 : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, ← pow_mul]
  simpa only [Nat.cast_ofNat] using (Complex.exp_nat_mul (((r / 4 : ℝ) : ℂ) * Complex.I) 4)

/-- A phase equals the two-square expression at one quarter of its exact quarter-turn remainder,
multiplied by the corresponding power of `I`. The remainder relation may use any integer and
does not assume that it was chosen by rounding. This is the analytic identity required by the
quarter-turn interval checker. -/
theorem exp_reduced_phase (x r : ℝ) (k : ℤ) (h : r = x - k * (Real.pi / 2)) :
    Complex.exp ((x : ℂ) * Complex.I) =
      (Complex.exp (((r / 4 : ℝ) : ℂ) * Complex.I) ^ 2) ^ 2 * Complex.I ^ k := by
  have hx : x = r + k * (Real.pi / 2) := by rw [h, sub_add_cancel]
  rw [hx, exp_quarter_turn, exp_phase_two_squares]

end PseudoPrime.Analysis
