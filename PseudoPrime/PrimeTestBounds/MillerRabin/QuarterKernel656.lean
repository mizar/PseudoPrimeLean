/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass
import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # Principal coefficient for the sixth-pole kernel through log 656 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The admissible sixth-pole kernel of section 132 has pole at -11/10 and shift 21/8. -/
noncomputable def quarterKernel656 : LLS.PaperStatements.MellinKernel :=
  LLS.PaperStatements.rationalPoleMellinKernel 3 (5 / 11) (21 / 16) (by norm_num only)
    (by norm_num only) (by norm_num only)

/-- The principal coefficient of the section 132 kernel exceeds 0.71780481.
Evaluate its unit-cutoff moment and half-point value, then bound both exponentials. -/
theorem quarter_principal_delta_656 :
    71780481 / 100000000 <
      4 * (∫ u : ℝ in (0 : ℝ)..1, (quarterKernel656.transform u).re / Real.sqrt u) -
        (quarterKernel656.function (1 / 2)).re := by
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_half_value,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (231 / 80 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hb :=
    Analysis.exp_le_taylor_add_two_next (x := (21 / 16 : ℝ)) (n := 20) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) ha
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  linarith only [hi, hb]

/-- The normalized boundary weight at the unit cutoff lies between 0.09319731 and 0.09319732. -/
theorem quarter_unit_weight_656 :
    9319731 / 100000000 < (quarterKernel656.transform 1).re ∧
      (quarterKernel656.transform 1).re < 9319732 / 100000000 := by
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ zero_lt_one,
    Complex.ofReal_re]
  norm_num only [Analysis.rationalPoleProfile, Real.log_one, sub_zero, Nat.factorial, ite_true,
    and_self, zero_lt_one]
  rw [Real.exp_neg, ← one_div]
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (231 / 80 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 231 / 80) 20
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hl := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hh := one_div_le_one_div_of_le (by norm_num only) hb
  constructor <;> linarith only [hl, hh]

/-- The constant pole recovery, after allowing three zeta masses of size
10⁻⁶, exceeds the rational mass saving in section 132. -/
theorem quarter_mass_constant_656 :
    (10.9219669 : ℝ) < 6 * (11 / 10) ^ 5 / ((11 / 10) ^ 2 - 1 / 4) ^ 3 - 3 / 1000000 := by
  norm_num only

/-- The new inverse transform on its support is the sixth-pole profile
with pole magnitude 11/10 and logarithmic shift 21/8. -/
theorem quarter_transform_656 {t : ℝ} (ht : 0 < t) (hs : Real.log t ≤ 21 / 8) :
    (quarterKernel656.transform t).re =
      (((11 / 10) * (21 / 8 - Real.log t)) ^ 5 * Real.exp (-((11 / 10) * (21 / 8 - Real.log t)))) /
        120 := by
  rw [quarterKernel656, LLS.PaperStatements.rationalPole_transform _ _ _ _ ht, Complex.ofReal_re]
  unfold Analysis.rationalPoleProfile
  rw [ite_eq_left ⟨ht, by linarith only [hs]⟩]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  have h : (21 / 8 - Real.log t) / (10 / 11) = (11 / 10) * (21 / 8 - Real.log t) := by ring
  rw [h]

/-- The Mellin function in the section 132 pole-magnitude normalization. -/
theorem quarter_function_656 (z : ℂ) :
    quarterKernel656.function z =
      (11 / 10) ^ 5 * Complex.exp ((21 / 8) * z) / (z + 11 / 10) ^ 6 := by
  change Analysis.rationalPoleFunction 3 (5 / 11) (21 / 16) z = _
  unfold Analysis.rationalPoleFunction
  norm_num only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, Nat.reduceMul]
  rw [show 1 + (10 / 11 : ℂ) * z = (10 / 11) * (z + 11 / 10) by ring, mul_pow, div_mul_eq_div_div]
  congr 1
  ring

/-- At scale X, the physical sixth-pole weight is the normalized profile at t/X
divided by the square root of the physical argument. -/
noncomputable def quarterWeight656 (X t : ℝ) : ℝ :=
  let v := (11 / 10) * (21 / 8 - Real.log (t / X))
  (1 / Real.sqrt t) * (v ^ 5 * Real.exp (-v) / 120)

/-- On its support the principal summand is the physical weight times
the von Mangoldt function. -/
theorem quarter_summand_656 {X : ℝ} (hX : 0 < X) {n : ℕ} (hn : 0 < n)
    (hs : Real.log ((n : ℝ) / X) ≤ 21 / 8) :
    (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re =
      quarterWeight656 X n * ArithmeticFunction.vonMangoldt n := by
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn.ne',
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [quarter_transform_656 (div_pos (Nat.cast_pos.mpr hn) hX) hs]
  unfold quarterWeight656
  ring

/-- At its cutoff, the physical weight is the unit mass divided by the square root. -/
theorem quarter_cutoff_weight_656 {X : ℝ} (hX : 0 < X) :
    quarterWeight656 X X = (quarterKernel656.transform 1).re / Real.sqrt X := by
  rw [quarter_transform_656 zero_lt_one (by norm_num only [Real.log_one])]
  unfold quarterWeight656
  rw [div_self hX.ne']
  ring

/-- The seven nonnegative displacements of the section 132 auxiliary frequencies
from the main shift. Indices follow the order in equation (132.5). -/
def quarterAuxShift656 (j : Fin 7) : ℚ :=
  ![0, 1 / 10, 21 / 10, 22 / 10, 43 / 10, 63 / 10, 64 / 10] j

/-- The exact seven coefficients used in the section 132 square completion.
The common denominator is one billion. -/
def quarterAuxCoeffRat656 (j : Fin 7) : ℚ :=
  (![553471189, -583719420, 121190904, -188329077, -12744582, 149546417, -133968795] j) / 1000000000

/-- Cast the exact rational coefficient into the real phase inequality. -/
noncomputable def quarterAuxCoeff656 (j : Fin 7) : ℝ :=
  quarterAuxCoeffRat656 j

/-- The actual auxiliary frequencies are the main shift plus the displacements. -/
noncomputable def quarterAuxFrequency656 (j : Fin 7) : ℝ :=
  21 / 8 + quarterAuxShift656 j

end PseudoPrime.PrimeTestBounds.MillerRabin
