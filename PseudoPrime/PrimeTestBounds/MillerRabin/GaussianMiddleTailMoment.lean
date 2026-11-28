/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleTailCutoff
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleMassTail

/-! # Finite moment reductions at a fixed Euler cutoff -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A padded coefficient row evaluates the shifted Euler moment by a finite sum.
The degree bound ensures all added terms are zero. -/
public theorem euler_moment_eq_row (P : Polynomial ℝ) (z s : ℝ) (N : ℕ) (f : ℕ → ℝ)
    (hN : P.natDegree ≤ N) (hf : ∀ i ≤ N, f i = (P.comp (Polynomial.X + Polynomial.C z)).coeff i) :
    eulerPolyMoment P z s =
      ∑ i ∈ Finset.range (N + 1), f i * ((i.factorial : ℝ) / s ^ (i + 1)) := by
  let S := P.comp (Polynomial.X + Polynomial.C z)
  have hS : S.natDegree ≤ N := by
    simpa only [S, Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one] using hN
  unfold eulerPolyMoment
  change (∑ i ∈ Finset.range (S.natDegree + 1), _) = _
  refine
    Eq.trans (Finset.sum_congr (g := fun i ↦ f i * ((i.factorial : ℝ) / s ^ (i + 1))) rfl ?_) ?_
  · intro i hi
    rw [hf i (Nat.le_of_lt_succ ((Finset.mem_range.mp hi).trans_le (Nat.succ_le_succ hS)))]
  · exact
      Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hS)) fun i hi hn ↦ by
        rw [hf i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)),
          Polynomial.coeff_eq_zero_of_natDegree_lt
            (Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h ↦ hn (Finset.mem_range.mpr h)))),
          zero_mul]

/-- At an exponential cutoff the two Euler moments separate into scalar
exponentials and finite coefficient sums. This form is used for rational certificates. -/
public theorem middle_mass_tail_at_exp (Q : Polynomial ℚ) (a : ℚ) (d : ℕ) (z : ℝ) :
    let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
    let H := Polynomial.X ^ 2 * (Polynomial.C ((a : ℝ) + 1 / 2) * P - P.derivative)
    middleMassTailCost Q a d (Real.exp z) =
      Real.exp (-((a : ℝ) - 1 / 2) * z) * eulerPolyMoment P z ((a : ℝ) - 1 / 2) +
        Real.exp (-(a : ℝ) * z) * (z ^ 2 * P.eval z + eulerPolyMoment H z (a : ℝ)) / 24 := by
  intro P H
  simp only [middleMassTailCost, Real.log_exp, Real.rpow_def_of_pos (Real.exp_pos z), P, H]
  rw [mul_comm z (-((a : ℝ) - 1 / 2)), mul_comm z (-(a : ℝ))]

/-- Compute the continuous main moment from the same shifted coefficient row
that supplies the Euler tail sign test. -/
public theorem middle_mass_tail_main_row (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ i ≤ d, f i = Q.coeff i) :
    eulerPolyMoment ((middleMassPolynomial Q a d).map (Rat.castHom ℝ)) (o : ℝ) ((a : ℝ) - 1 / 2) =
      ∑ i ∈ Finset.range (d + 2),
        ((middleMassShiftRow a o d f)[i]?.getD 0 : ℝ) *
          ((i.factorial : ℝ) / ((a : ℝ) - 1 / 2) ^ (i + 1)) := by
  refine euler_moment_eq_row _ _ _ (d + 1) _ ?_ (fun i _ ↦ ?_)
  · rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact middle_mass_poly_degree Q a d
  · rw [middle_mass_shift_coeff Q a o d f hQ hf]
    have he :=
      congrArg (fun P : Polynomial ℝ ↦ P.coeff i)
        (Polynomial.map_comp (Rat.castHom ℝ) (middleMassPolynomial Q a d)
          (Polynomial.X + Polynomial.C o))
    simpa only [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Polynomial.coeff_map,
      Rat.coe_castHom] using he

/-- Shift the RH derivative charge by differentiating the already shifted mass.
This identity avoids a second affine transformation for the error term. -/
private theorem tail_charge_shift (P : Polynomial ℝ) (a o : ℝ) :
    let V := Polynomial.X + Polynomial.C o
    let S := P.comp V
    (Polynomial.X ^ 2 * (Polynomial.C (a + 1 / 2) * P - P.derivative)).comp V =
      V ^ 2 * (Polynomial.C (a + 1 / 2) * S - S.derivative) := by
  intro V S
  simp only [S, V, Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.sub_comp,
    Polynomial.C_comp, Polynomial.derivative_comp, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, one_mul]

/-- The error moment uses a padded finite sum from the shifted mass and its
derivative. The only added polynomial factor is the shifted logarithmic square. -/
public theorem middle_tail_error_sum (P : Polynomial ℝ) (a o : ℝ) (N : ℕ) (hN : P.natDegree ≤ N) :
    let V := Polynomial.X + Polynomial.C o
    let S := P.comp V
    eulerPolyMoment (Polynomial.X ^ 2 * (Polynomial.C (a + 1 / 2) * P - P.derivative)) o a =
      ∑ i ∈ Finset.range (N + 3),
        (V ^ 2 * (Polynomial.C (a + 1 / 2) * S - S.derivative)).coeff i *
          ((i.factorial : ℝ) / a ^ (i + 1)) := by
  intro V S
  refine euler_moment_eq_row _ _ _ (N + 2) _ ?_ (fun i _ ↦ ?_)
  · refine Polynomial.natDegree_mul_le.trans (add_le_add ?_ ?_) |>.trans_eq (add_comm 2 N)
    · exact (Polynomial.natDegree_X_pow _).le
    · refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
      · exact
          Polynomial.natDegree_mul_le.trans
            (by simpa only [Polynomial.natDegree_C, zero_add] using hN)
      · exact (Polynomial.natDegree_derivative_le P).trans ((Nat.sub_le _ _).trans hN)
  · exact congrArg (fun T : Polynomial ℝ ↦ T.coeff i) (tail_charge_shift P a o).symm

/-- Express the full Abel cost at a rational logarithmic cutoff using a single
shifted mass polynomial, its coefficient row, and two scalar exponentials. -/
public theorem middle_mass_tail_sums (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ i ≤ d, f i = Q.coeff i) :
    let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
    let V := Polynomial.X + Polynomial.C (o : ℝ)
    let S := P.comp V
    let c := fun i : ℕ ↦ ((middleMassShiftRow a o d f)[i]?.getD 0 : ℝ)
    let H := V ^ 2 * (Polynomial.C ((a : ℝ) + 1 / 2) * S - S.derivative)
    middleMassTailCost Q a d (Real.exp (o : ℝ)) =
      Real.exp (-((a : ℝ) - 1 / 2) * (o : ℝ)) *
          (∑ i ∈ Finset.range (d + 2), c i * ((i.factorial : ℝ) / ((a : ℝ) - 1 / 2) ^ (i + 1))) +
        Real.exp (-(a : ℝ) * (o : ℝ)) *
            ((o : ℝ) ^ 2 * P.eval (o : ℝ) +
              ∑ i ∈ Finset.range (d + 4), H.coeff i * ((i.factorial : ℝ) / (a : ℝ) ^ (i + 1))) /
          24 := by
  intro P V S c H
  have hN : P.natDegree ≤ d + 1 := by
    change ((middleMassPolynomial Q a d).map (Rat.castHom ℝ)).natDegree ≤ d + 1
    rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact middle_mass_poly_degree Q a d
  rw [middle_mass_tail_at_exp, middle_mass_tail_main_row Q a o d f hQ hf,
    middle_tail_error_sum P (a : ℝ) (o : ℝ) (d + 1) hN]

/-- Multiplication by the shifted logarithmic square uses only three adjacent
entries of the derivative charge row. Indices below zero contribute zero. -/
public theorem tail_square_coeff (T : Polynomial ℝ) (o : ℝ) (i : ℕ) :
    ((Polynomial.X + Polynomial.C o) ^ 2 * T).coeff i =
      (if 2 ≤ i then T.coeff (i - 2) else 0) + 2 * o * (if 1 ≤ i then T.coeff (i - 1) else 0) +
        o ^ 2 * T.coeff i := by
  have he :
    (Polynomial.X + Polynomial.C o) ^ 2 =
      Polynomial.X ^ 2 + Polynomial.C (2 * o) * Polynomial.X ^ 1 + Polynomial.C (o ^ 2) := by
    simp only [Polynomial.C_mul, Polynomial.C_pow, Polynomial.C_ofNat]
    ring
  rw [he, add_mul, add_mul, mul_assoc]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']

/-- The shifted RH derivative charge at a coefficient is a two-entry difference
in the original shifted row. The result also applies to zero-padded entries. -/
public theorem tail_derivative_coeff (S : Polynomial ℝ) (a : ℝ) (i : ℕ) :
    (Polynomial.C (a + 1 / 2) * S - S.derivative).coeff i =
      (a + 1 / 2) * S.coeff i - (i + 1 : ℕ) * S.coeff (i + 1) := by
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative, Nat.cast_succ,
    mul_comm (S.coeff (i + 1))]

/-- The main Euler moment at rate `s`, computed from a zero-padded rational row. -/
public def middleTailRowMoment (N : ℕ) (s : ℚ) (c : ℕ → ℚ) : ℚ :=
  ∑ i ∈ Finset.range (N + 1), c i * ((i.factorial : ℚ) / s ^ (i + 1))

/-- The boundary and derivative costs at logarithmic cutoff `o`, computed
from the zero-padded mass row with neighboring coefficient differences. -/
public def middleTailRowError (N : ℕ) (a o : ℚ) (c : ℕ → ℚ) : ℚ :=
  let t := fun i : ℕ ↦ (a + 1 / 2) * c i - (i + 1 : ℕ) * c (i + 1)
  o ^ 2 * c 0 +
    middleTailRowMoment (N + 2) a
      (fun i ↦
        (if 2 ≤ i then t (i - 2) else 0) + 2 * o * (if 1 ≤ i then t (i - 1) else 0) + o ^ 2 * t i)

/-- Two rational scalars from the shifted row supply the complete Abel cost
after multiplication by the corresponding real exponential factors. -/
public theorem middle_mass_tail_rat (Q : Polynomial ℚ) (a o : ℚ) (d : ℕ) (f : ℕ → ℚ)
    (hQ : Q.natDegree ≤ d) (hf : ∀ i ≤ d, f i = Q.coeff i) :
    let c := fun i : ℕ ↦ (middleMassShiftRow a o d f)[i]?.getD 0
    middleMassTailCost Q a d (Real.exp (o : ℝ)) =
      Real.exp (-((a : ℝ) - 1 / 2) * (o : ℝ)) * (middleTailRowMoment (d + 1) (a - 1 / 2) c : ℝ) +
        Real.exp (-(a : ℝ) * (o : ℝ)) * (middleTailRowError (d + 1) a o c : ℝ) / 24 := by
  intro c
  let P := (middleMassPolynomial Q a d).map (Rat.castHom ℝ)
  let S := P.comp (Polynomial.X + Polynomial.C (o : ℝ))
  have hc (i : ℕ) : (c i : ℝ) = S.coeff i := by
    rw [show c i = (middleMassShiftRow a o d f)[i]?.getD 0 from rfl,
      middle_mass_shift_coeff Q a o d f hQ hf]
    have he :=
      congrArg (fun T : Polynomial ℝ ↦ T.coeff i)
        (Polynomial.map_comp (Rat.castHom ℝ) (middleMassPolynomial Q a d)
          (Polynomial.X + Polynomial.C o))
    simpa only [S, P, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Polynomial.coeff_map,
      Rat.coe_castHom] using he
  have h0 : (c 0 : ℝ) = P.eval (o : ℝ) := by
    rw [hc, Polynomial.coeff_zero_eq_eval_zero]
    simp only [S, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
      zero_add]
  rw [middle_mass_tail_sums Q a o d f hQ hf]
  simp only [middleTailRowError, middleTailRowMoment, Rat.cast_sum, Rat.cast_add, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast, h0,
    tail_square_coeff, tail_derivative_coeff, apply_ite, Rat.cast_zero]
  have hc' (i : ℕ) : ((middleMassShiftRow a o d f)[i]?.getD 0 : ℝ) = S.coeff i := hc i
  simp only [hc, hc', S, P, Rat.cast_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
