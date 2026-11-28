/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighGammaCoefficients
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighProfileSign

/-! # Bernstein bounds for the high Gaussian gamma polynomial -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The gamma upper polynomial has no terms beyond the physical profile
degree bound, since derivatives and constant multiples preserve that bound. -/
theorem high_gamma_upper_poly_degree (K : HighGaussianKernel) (N : ℕ) :
    (highGammaUpperPoly K N).natDegree ≤ 2 * K.degree + 3 := by
  rw [highGammaUpperPoly]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (high_rat_profile_degree K)
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact
      (Polynomial.natDegree_C_mul_le _ _).trans
        ((Polynomial.natDegree_iterate_derivative _ j).trans
          ((Nat.sub_le _ _).trans (high_rat_profile_degree K)))

/-- Compute the affine power row for the gamma polynomial on a cell
starting at `l` with width `h`, sharing the original rational row. -/
def highGammaCellPowerRow (K : HighGaussianKernel) (N : ℕ) (l h : ℚ) : Array ℚ :=
  let row := highGammaUpperRow K N
  let m := 2 * K.degree + 4
  Array.ofFn
    (fun k : Fin m ↦
      h ^ k.val *
        ∑ j ∈ Finset.range m, row[j]?.getD 0 * ((Nat.fast_choose j k.val : ℚ) * l ^ (j - k.val)))

/-- The affine row agrees entry by entry with the coefficients of the
analytic upper polynomial restricted to the cell. -/
theorem high_gamma_cell_power_coeff (K : HighGaussianKernel) (N : ℕ) (l h : ℚ) {k : ℕ}
    (hk : k < 2 * K.degree + 4) :
    (highGammaCellPowerRow K N l h)[k]?.getD 0 =
      ((highGammaUpperPoly K N).comp (Polynomial.C h * Polynomial.X + Polynomial.C l)).coeff k := by
  rw [Analysis.rational_affine_coeff _ _ (high_gamma_upper_poly_degree K N)]
  simp only [highGammaCellPowerRow, Array.getElem?_ofFn, dite_eq_left hk, Option.getD_some]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [high_gamma_upper_row_coeff K N (Finset.mem_range.mp hj)]

/-- Compute the Bernstein row on a cell from one shared affine power row. -/
def highGammaCellBernsteinRow (K : HighGaussianKernel) (N : ℕ) (l h : ℚ) : Array ℚ :=
  let row := highGammaCellPowerRow K N l h
  Array.ofFn (fun i : Fin (2 * K.degree + 4) ↦ cellBernsteinFromPower (2 * K.degree + 3) i.val row)

/-- The executable Bernstein coefficient represents the gamma polynomial
on the affine unit cell. -/
theorem high_gamma_cell_bernstein (K : HighGaussianKernel) (N : ℕ) (l h : ℚ) {i : ℕ}
    (hi : i < 2 * K.degree + 4) :
    Analysis.bernsteinRatCoeff
        ((highGammaUpperPoly K N).comp (Polynomial.C h * Polynomial.X + Polynomial.C l))
        (2 * K.degree + 3) i =
      (highGammaCellBernsteinRow K N l h)[i]?.getD 0 := by
  simp only [Analysis.bernsteinRatCoeff, highGammaCellBernsteinRow, Array.getElem?_ofFn,
    dite_eq_left hi, Option.getD_some, cellBernsteinFromPower]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k ≤ i
  · rw [ite_eq_left hki, high_gamma_cell_power_coeff K N l h (Finset.mem_range.mp hk)]
  · simp only [ite_eq_right hki, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hki), Nat.cast_zero, zero_div, mul_zero]

/-- A common rational bound on the computed Bernstein row bounds the
gamma upper polynomial at every point in the corresponding real cell. -/
theorem high_gamma_upper_cell_le (K : HighGaussianKernel) (N : ℕ) {l r M : ℚ} (hlr : l < r) {z : ℝ}
    (hz : z ∈ Set.Icc (l : ℝ) (r : ℝ))
    (hM : ∀ i < 2 * K.degree + 4, (highGammaCellBernsteinRow K N l (r - l))[i]?.getD 0 ≤ M) :
    (highGammaUpperPoly K N).eval₂ (Rat.castHom ℝ) z ≤ (M : ℝ) := by
  refine
    Analysis.bernstein_interval_le (Rat.cast_lt.mpr hlr) hz.1 hz.2
      (fun x ↦ (highGammaUpperPoly K N).eval₂ (Rat.castHom ℝ) x) (2 * K.degree + 3)
      (fun i ↦ ((highGammaCellBernsteinRow K N l (r - l))[i.val]?.getD 0 : ℝ)) _
      (fun i ↦ Rat.cast_le.mpr (hM i i.isLt)) ?_
  intro t
  have h :=
    Analysis.bernstein_rat_affine_eval (highGammaUpperPoly K N) (2 * K.degree + 3)
      (high_gamma_upper_poly_degree K N) l r t
  have hc (i : Fin (2 * K.degree + 4)) := high_gamma_cell_bernstein K N l (r - l) i.isLt
  simpa only [hc, Rat.cast_sub, add_comm (l : ℝ)] using h

/-- If all translated gamma coefficients are nonpositive, the gamma
upper polynomial is nonpositive on the entire half-line from that cutoff. -/
theorem high_gamma_poly_nonpos_of_shift (K : HighGaussianKernel) (N : ℕ) (a : ℚ)
    (h : ∀ i < 2 * K.degree + 4, (highGammaCellPowerRow K N a 1)[i]?.getD 0 ≤ 0) {z : ℝ}
    (hz : (a : ℝ) ≤ z) : ((highGammaUpperPoly K N).map (Rat.castHom ℝ)).eval z ≤ 0 := by
  let P := highGammaUpperPoly K N
  let Q := P.comp (Polynomial.X + Polynomial.C a)
  have hdeg : Q.natDegree ≤ 2 * K.degree + 3 := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa only [Polynomial.natDegree_X_add_C, mul_one] using high_gamma_upper_poly_degree K N
  have hQ (i : ℕ) : Q.coeff i ≤ 0 := by
    by_cases hi : i < 2 * K.degree + 4
    · have he := high_gamma_cell_power_coeff K N a 1 hi
      simp only [Polynomial.C_1, one_mul] at he
      exact he ▸ h i hi
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (hdeg.trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hi)))]
  have hs :
    ∀ i, 0 ≤ ((Polynomial.C (1 : ℚ) * -P).comp (Polynomial.X + Polynomial.C a)).coeff i := by
    intro i
    simpa only [Polynomial.C_1, one_mul, Polynomial.neg_comp, Polynomial.coeff_neg] using
      neg_nonneg.mpr (hQ i)
  have hp := profile_shift_nonneg_of_scaled (-P) a zero_lt_one hs 0 hz
  simpa only [Function.iterate_zero_apply, Polynomial.map_neg, Polynomial.eval_neg,
    neg_nonneg] using hp

/-- The derivative commutes with a unit-width translation. -/
private theorem gamma_translate_derivative (P : Polynomial ℚ) (a : ℚ) (j : ℕ) :
    ((Polynomial.derivative^[j]) P).comp (Polynomial.X + Polynomial.C a) =
      (Polynomial.derivative^[j]) (P.comp (Polynomial.X + Polynomial.C a)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Function.iterate_succ_apply', ← ih, Polynomial.derivative_comp,
      Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
      one_mul]

/-- Translate the profile first and apply the gamma weights to its derivatives. -/
def highGammaTranslatedRow (K : HighGaussianKernel) (N : ℕ) (a : ℚ) : Array ℚ :=
  let m := 2 * K.degree + 4
  let B := K.cellPowerRow a 1
  let U := Array.ofFn (fun j : Fin m ↦ (highGammaBounds K N j.val).2)
  Array.ofFn
    (fun k : Fin m ↦
      (4 / 3 : ℚ) * B[k.val]?.getD 0 +
        ∑ j ∈ Finset.range m,
          U[j]?.getD 0 * ((k.val + j).descFactorial j : ℚ) * B[k.val + j]?.getD 0)

/-- The translated profile row gives the same coefficients as translating
the full gamma upper polynomial. -/
theorem high_gamma_translated_coeff (K : HighGaussianKernel) (N : ℕ) (a : ℚ) {k : ℕ}
    (hk : k < 2 * K.degree + 4) :
    (highGammaTranslatedRow K N a)[k]?.getD 0 =
      ((highGammaUpperPoly K N).comp (Polynomial.X + Polynomial.C a)).coeff k := by
  let Q := K.ratProfile.comp (Polynomial.X + Polynomial.C a)
  have hd : Q.natDegree ≤ 2 * K.degree + 3 := by
    refine Polynomial.natDegree_comp_le.trans ?_
    simpa only [Polynomial.natDegree_X_add_C, mul_one] using high_rat_profile_degree K
  have hb (i : ℕ) : (K.cellPowerRow a 1)[i]?.getD 0 = Q.coeff i := by
    by_cases hi : i < 2 * K.degree + 4
    · simpa only [Q, Polynomial.C_1, one_mul] using high_cell_power_coeff K a 1 hi
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
          (hd.trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hi)))]
      simp only [HighGaussianKernel.cellPowerRow, Array.getElem?_ofFn, dite_eq_right hi,
        Option.getD_none]
  simp only [highGammaTranslatedRow, Array.getElem?_ofFn, dite_eq_left hk, Option.getD_some,
    highGammaUpperPoly, Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.sum_comp, gamma_translate_derivative, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.finsetSum_coeff, Polynomial.coeff_iterate_derivative]
  dsimp only [Q] at hb
  rw [hb]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  simp only [dite_eq_left hj', Option.getD_some, hb, nsmul_eq_mul, mul_assoc]

/-- Check the translated coefficients in one pass over the computed row. -/
def highGammaShiftNonpos (K : HighGaussianKernel) (N : ℕ) (a : ℚ) : Bool :=
  (highGammaTranslatedRow K N a).all (fun q ↦ decide (q ≤ 0))

/-- A passing translated-row check certifies the upper polynomial
for every height beyond the cutoff. -/
theorem high_gamma_shift_nonpos_sound (K : HighGaussianKernel) (N : ℕ) (a : ℚ)
    (h : highGammaShiftNonpos K N a = true) {z : ℝ} (hz : (a : ℝ) ≤ z) :
    ((highGammaUpperPoly K N).map (Rat.castHom ℝ)).eval z ≤ 0 := by
  apply high_gamma_poly_nonpos_of_shift K N a _ hz
  intro i hi
  have hi' : i < (highGammaTranslatedRow K N a).size := by
    simpa only [highGammaTranslatedRow, Array.size_ofFn] using hi
  rw [high_gamma_cell_power_coeff K N a 1 hi, Polynomial.C_1, one_mul, ←
    high_gamma_translated_coeff K N a hi, Array.getElem?_eq_getElem hi', Option.getD_some]
  exact of_decide_eq_true (Array.all_eq_true.mp h i hi')

end PseudoPrime.PrimeTestBounds.MillerRabin
