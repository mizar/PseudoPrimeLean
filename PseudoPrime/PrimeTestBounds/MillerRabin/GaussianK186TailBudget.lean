/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186TailTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailMoment
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailBudget

/-! # The fixed far Euler budget for K186 -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Shift the shared K186 mass coefficients to logarithmic cutoff 53. -/
private def farMassRow : Array ℚ :=
  shiftedMassCoeffTable .k186 53

/-- Extract a zero-padded coefficient from the shared far mass row. -/
private def farCoeff (i : ℕ) : ℚ :=
  farMassRow[i]?.getD 0

/-- The rational row is the coefficient table of the shifted real mass. -/
private theorem far_coeff_eq (i : ℕ) :
    (farCoeff i : ℝ) = (k186MassPoly.comp (Polynomial.X + Polynomial.C 53)).coeff i := by
  rw [farCoeff, farMassRow, shifted_mass_entry]
  have he :=
    congrArg (fun P : Polynomial ℝ ↦ P.coeff i)
      (Polynomial.map_comp (Rat.castHom ℝ) (highGaussianMassPolynomial .k186)
        (Polynomial.X + Polynomial.C (53 : ℚ)))
  simpa only [k186MassPoly, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.coeff_map, Rat.coe_castHom, Rat.cast_ofNat] using he

/-- The K186 mass degree permits exactly 42 entries. -/
private theorem far_mass_degree : k186MassPoly.natDegree ≤ 41 := by
  rw [k186MassPoly, Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
  simpa only [Polynomial.C_0, add_zero, Polynomial.comp_X, HighGaussianKernel.degree] using
    high_mass_shifted_degree .k186 0

/-- The real envelope at the fixed cutoff uses two rational row moments. -/
private theorem far_tail_row_eq :
    k186TailCost (Real.exp 53) =
      Real.exp (-(9 / 4 : ℝ) * 53) * (middleTailRowMoment 41 (9 / 4) farCoeff : ℝ) +
        Real.exp (-(11 / 4 : ℝ) * 53) * (middleTailRowError 41 (11 / 4) 53 farCoeff : ℝ) / 24 := by
  have hM :=
    euler_moment_eq_row k186MassPoly 53 (9 / 4) 41 (fun i ↦ (farCoeff i : ℝ)) far_mass_degree
      (fun i _ ↦ far_coeff_eq i)
  have hE := middle_tail_error_sum k186MassPoly (11 / 4) 53 41 far_mass_degree
  have h0 : (farCoeff 0 : ℝ) = k186MassPoly.eval 53 := by
    rw [far_coeff_eq, Polynomial.coeff_zero_eq_eval_zero]
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
  have ha : (11 / 4 : ℝ) + 1 / 2 = 13 / 4 := by norm_num only
  have hd (i : ℕ) :=
    tail_derivative_coeff (k186MassPoly.comp (Polynomial.X + Polynomial.C 53)) (11 / 4) i
  rw [ha] at hd
  rw [ha] at hE
  simp only [k186TailCost, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos (53 : ℝ))]
  rw [hM, hE, mul_comm (53 : ℝ) (-(9 / 4 : ℝ)), mul_comm (53 : ℝ) (-(11 / 4 : ℝ))]
  simp only [middleTailRowError, middleTailRowMoment, Rat.cast_sum, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, h0,
    tail_square_coeff, hd, ha, apply_ite, Rat.cast_zero, Rat.cast_one, far_coeff_eq]

/-- The fixed main moment is below a rounded integer cap. -/
private theorem far_main_check : middleTailRowMoment 41 (9 / 4) farCoeff ≤ 3 * 10 ^ 42 := by
  decide +kernel

/-- The fixed boundary and RH derivative terms fit the error cap. -/
private theorem far_error_check : middleTailRowError 41 (11 / 4) 53 farCoeff ≤ 3 * 10 ^ 46 := by
  decide +kernel

/-- At logarithmic cutoff 53, the full K186 right Euler budget is at most
one hundred-millionth. The fixed bound can be reused at all larger cutoffs. -/
public theorem k186_far_tail_budget : 4 * k186TailCost (Real.exp 53) ≤ 1 / 10 ^ 8 := by
  have en := middle_tail_exp_le 9540 (by decide +kernel)
  have em := middle_tail_exp_le 11660 (by decide +kernel)
  simp only [Nat.cast_ofNat] at en em
  rw [show (9540 : ℝ) / 80 = (9 / 4) * 53 by norm_num only, ← neg_mul] at en
  rw [show (11660 : ℝ) / 80 = (11 / 4) * 53 by norm_num only, ← neg_mul] at em
  have hM :=
    (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr far_main_check)
          (Real.exp_pos (-(9 / 4 : ℝ) * 53)).le).trans
      (mul_le_mul_of_nonneg_right en
        (Rat.cast_nonneg.mpr (by decide +kernel : (0 : ℚ) ≤ 3 * 10 ^ 42)))
  have hE :=
    (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr far_error_check)
          (Real.exp_pos (-(11 / 4 : ℝ) * 53)).le).trans
      (mul_le_mul_of_nonneg_right em
        (Rat.cast_nonneg.mpr (by decide +kernel : (0 : ℚ) ≤ 3 * 10 ^ 46)))
  have hb :
    (4 : ℝ) *
        (3 * 10 ^ 42 / (middleTailExpDen 9540 : ℝ) +
          3 * 10 ^ 46 / (middleTailExpDen 11660 : ℝ) / 24) ≤
      1 / 10 ^ 8 := by
    have h :
      (4 : ℚ) * (3 * 10 ^ 42 / middleTailExpDen 9540 + 3 * 10 ^ 46 / middleTailExpDen 11660 / 24) ≤
        1 / 10 ^ 8 := by
      decide +kernel
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_one] using (Rat.cast_le (K := ℝ)).mpr h
  rw [far_tail_row_eq]
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, one_div, Rat.cast_inv] at hM hE
  simp only [div_eq_mul_inv] at hM hE hb ⊢
  linear_combination 4 * hM + (1 / 6 : ℝ) * hE + hb

end PseudoPrime.PrimeTestBounds.MillerRabin
