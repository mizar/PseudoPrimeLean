/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerPolyRH
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassProfile
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighMassCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassCoeffs

/-! # Eventual signs and Abel bounds for the middle Euler tail -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Balance of the two poles bounds the degree of the mass polynomial by `d + 1`. -/
public theorem middle_mass_poly_degree (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) :
    (middleMassPolynomial Q a d).natDegree ≤ d + 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp only [middleMassPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  apply Finset.sum_eq_zero
  intro j _
  rw [opposite_pole_coeff_eq,
    opposite_coeff_eq_zero a _ _ _ ((Nat.sub_le (d + 2) j).trans (Nat.succ_le_of_lt hi)), mul_zero]

/-- Shift the mass coefficient row once to the left endpoint of the tail. -/
public def middleMassShiftRow (a o : ℚ) (d : ℕ) (f : ℕ → ℚ) : Array ℚ :=
  let row := middleMassCoeffRow a d f
  gaussianShiftRatRow (d + 1) o (fun j ↦ row[j]?.getD 0)

/-- The entire shifted row agrees with the translated polynomial, including zero padding. -/
public theorem middle_mass_shift_coeff (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k) (i : ℕ) :
    (middleMassShiftRow a o d f)[i]?.getD 0 =
      ((middleMassPolynomial Q a d).comp (Polynomial.X + Polynomial.C o)).coeff i := by
  by_cases hi : i < d + 2
  · exact
      gaussian_shift_rat_coeff _ _ _ _ (middle_mass_poly_degree Q a d)
        (fun _ hj ↦ middle_mass_coeff_row_eq Q a d f hQ hf (Nat.lt_succ_of_le hj))
        (Nat.le_of_lt_succ hi)
  · have hdeg :
      ((middleMassPolynomial Q a d).comp (Polynomial.X + Polynomial.C o)).natDegree ≤ d + 1 := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
      exact middle_mass_poly_degree Q a d
    simp only [middleMassShiftRow, gaussianShiftRatRow, Array.getElem?_ofFn, dite_eq_right hi,
      Option.getD_none,
      Polynomial.coeff_eq_zero_of_natDegree_lt
          (hdeg.trans_lt (Nat.lt_of_succ_le (Nat.le_of_not_gt hi)))]

/-- From the shifted row read both the mass and its signed derivative charge. -/
public def middleMassTailSigns (a o : ℚ) (d : ℕ) (f : ℕ → ℚ) : Prop :=
  let row := middleMassShiftRow a o d f
  ∀ i : Fin (d + 2),
    0 ≤ row[i.val]?.getD 0 ∧
      0 ≤ (a + 1 / 2) * row[i.val]?.getD 0 - (i.val + 1 : ℕ) * row[i.val + 1]?.getD 0

/-- The translated coefficient test establishes positivity of the mass
and its derivative charge everywhere on the tail. -/
public theorem middle_mass_tail_signs (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k) (hs : middleMassTailSigns a o d f)
    {z : ℝ} (hz : (o : ℝ) ≤ z) :
    let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
    0 ≤ P.eval z ∧ 0 ≤ (Polynomial.C ((a : ℝ) + 1 / 2) * P - P.derivative).eval z := by
  intro P
  let row := middleMassShiftRow a o d f
  let V := Polynomial.X + Polynomial.C (o : ℝ)
  let S := P.comp V
  have hS :
    S =
      ((middleMassPolynomial Q a d).comp (Polynomial.X + Polynomial.C o)).map (Rat.castHom ℝ) := by
    simp only [S, V, P, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom]
  have he (i : ℕ) : S.coeff i = (row[i]?.getD 0 : ℝ) := by
    rw [hS, Polynomial.coeff_map, Rat.coe_castHom, middle_mass_shift_coeff Q a o d f hQ hf]
  have hzero (i : ℕ) (hi : d + 2 ≤ i) : row[i]?.getD 0 = 0 := by
    simp only [row, middleMassShiftRow, gaussianShiftRatRow, Array.getElem?_ofFn,
      dite_eq_right (Nat.not_lt_of_ge hi), Option.getD_none]
  have hn (i : ℕ) :
    0 ≤ S.coeff i ∧ 0 ≤ (Polynomial.C ((a : ℝ) + 1 / 2) * S - S.derivative).coeff i := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative, he, he]
    by_cases hi : i < d + 2
    · have h := hs ⟨i, hi⟩
      refine ⟨Rat.cast_nonneg.mpr h.1, ?_⟩
      rw [mul_comm (row[i + 1]?.getD 0 : ℝ)]
      simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_one, Rat.cast_natCast, Nat.cast_add, Nat.cast_one] using
        (Rat.cast_nonneg (K := ℝ)).mpr h.2
    · have hi' := Nat.le_of_not_gt hi
      rw [hzero i hi', hzero (i + 1) (hi'.trans (Nat.le_succ i))]
      simp only [Rat.cast_zero, mul_zero, zero_mul, sub_zero, le_refl, and_self]
  have hp (U : Polynomial ℝ) (hU : ∀ i, 0 ≤ U.coeff i) : 0 ≤ U.eval (z - (o : ℝ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hU i) (pow_nonneg (sub_nonneg.mpr hz) _)
  have hu := hp S (fun i ↦ (hn i).1)
  have hv := hp (Polynomial.C ((a : ℝ) + 1 / 2) * S - S.derivative) (fun i ↦ (hn i).2)
  simp only [S, V, Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_C,
    Polynomial.derivative_X, add_zero, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X, one_mul,
    sub_add_cancel] at hu hv ⊢
  exact ⟨hu, hv⟩

/-- The Abel envelope consists of the continuous main moment, the cutoff
boundary term, and the RH derivative moment. -/
public noncomputable def middleMassTailCost (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (X : ℝ) : ℝ :=
  let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
  let z := Real.log X
  let H := Polynomial.X ^ 2 * (Polynomial.C ((a : ℝ) + 1 / 2) * P - P.derivative)
  X ^ (-((a : ℝ) - 1 / 2)) * eulerPolyMoment P z ((a : ℝ) - 1 / 2) +
    X ^ (-(a : ℝ)) * (z ^ 2 * P.eval z + eulerPolyMoment H z (a : ℝ)) / 24

/-- Bound the signed mass tail in the three-character formula using
the coefficient test and the existing RH Abel estimate. -/
public theorem middle_mass_tail_rh (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (ha : 2 ≤ (a : ℝ)) (hQ : Q.natDegree ≤ d) (hf : ∀ k ≤ d, f k = Q.coeff k)
    (hs : middleMassTailSigns a o d f) (hRH : RiemannHypothesis) {X : ℝ} (hX : 101 ≤ X)
    (hx : 1 ≤ Real.log X) (ho : (o : ℝ) ≤ Real.log X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          α n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile Q a d n.val)) ≤
      4 * middleMassTailCost Q a d X := by
  rw [middle_mass_tail_polynomial Q a d ha]
  let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
  have h :=
    euler_trace_tail_rh P (σ := (a : ℝ) + 1 / 2) (by linarith only [ha]) hRH hX hx
      (fun z hz ↦ (middle_mass_tail_signs Q a o d f hQ hf hs (ho.trans hz)).1)
      (fun z hz ↦ (middle_mass_tail_signs Q a o d f hQ hf hs (ho.trans hz)).2) α hα
  have h₁ : (a : ℝ) + 1 / 2 - 1 = (a : ℝ) - 1 / 2 := by ring
  have h₂ : (a : ℝ) + 1 / 2 - 1 / 2 = (a : ℝ) := by ring
  have h₃ : -((a : ℝ) + 1 / 2) = -(a : ℝ) - 1 / 2 := by ring
  simpa only [h₁, h₂, h₃, P, middleMassTailCost, Polynomial.eval_map, mul_assoc,
    mul_left_comm] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
