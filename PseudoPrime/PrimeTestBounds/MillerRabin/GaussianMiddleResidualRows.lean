/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleRationalLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntCurvature
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleRationalLower

/-! # Shared integer rows for the rational middle residual -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Scale an integer row by a rational without normalizing individual entries. -/
@[expose]
public def MiddleIntRow.scaleRat (r : MiddleIntRow) (q : ℚ) : MiddleIntRow :=
  r.scale q.num q.den

/-- Interpret row scaling as multiplication by a constant polynomial. -/
public theorem MiddleIntRow.poly_scaleRat (r : MiddleIntRow) (q : ℚ) (N : ℕ) :
    (r.scaleRat q).poly N = Polynomial.C q * r.poly N := by
  rw [MiddleIntRow.scaleRat, MiddleIntRow.poly_scale, Int.cast_natCast, Rat.num_div_den]

/-- Row scaling preserves a positive common denominator. -/
public theorem MiddleIntRow.scaleRat_pos {r : MiddleIntRow} (hr : 0 < r.den) (q : ℚ) :
    0 < (r.scaleRat q).den := by exact mul_pos hr (Int.natCast_pos.mpr q.den_pos)

/-- The first residual row combines already translated profile and moment rows.
Only three scalar multiplications and two row additions are needed. -/
@[expose]
public def middleEulerCostRow (N : ℕ) (a p : ℚ) (B M R : MiddleIntRow) : MiddleIntRow :=
  ((R.scaleRat (6 * p)).add N (M.scaleRat (3 * p))).add N
    (B.scaleRat (3 * p * (839 / 1000 + (a - 1 / 2))))

/-- The first residual row has a positive common denominator. -/
public theorem middle_euler_row_den_pos (N : ℕ) (a p : ℚ) {B M R : MiddleIntRow} (hB : 0 < B.den)
    (hM : 0 < M.den) (hR : 0 < R.den) : 0 < (middleEulerCostRow N a p B M R).den := by
  exact mul_pos (mul_pos (R.scaleRat_pos hR _) (M.scaleRat_pos hM _)) (B.scaleRat_pos hB _)

/-- The integer Euler row represents the sum of the two translated moment
polynomials and the translated profile with the rational endpoint cost. -/
public theorem middle_euler_cost_row_poly (N : ℕ) (a p : ℚ) (B M R : MiddleIntRow) (hB : 0 < B.den)
    (hM : 0 < M.den) (hR : 0 < R.den) :
    (middleEulerCostRow N a p B M R).poly N =
      Polynomial.C (6 * p) * R.poly N + Polynomial.C (3 * p) * M.poly N +
        Polynomial.C (3 * p * (839 / 1000 + (a - 1 / 2))) * B.poly N := by
  have hb := (B.scaleRat_pos hB (3 * p * (839 / 1000 + (a - 1 / 2)))).ne'
  have hm := (M.scaleRat_pos hM (3 * p)).ne'
  have hr := (R.scaleRat_pos hR (6 * p)).ne'
  have hsum : ((R.scaleRat (6 * p)).add N (M.scaleRat (3 * p))).den ≠ 0 := mul_ne_zero hr hm
  rw [middleEulerCostRow, MiddleIntRow.poly_add _ _ _ hsum hb, MiddleIntRow.poly_add _ _ _ hr hm,
    MiddleIntRow.poly_scaleRat, MiddleIntRow.poly_scaleRat, MiddleIntRow.poly_scaleRat]

/-- With its input transforms verified once, the shared integer Euler row
evaluates the first rational residual profile at every local coordinate. -/
public theorem middle_euler_row_eval (N : ℕ) (a p : ℚ) (b o : ℝ) (B M R : MiddleIntRow)
    (P Q : Polynomial ℝ) (hB : 0 < B.den) (hM : 0 < M.den) (hR : 0 < R.den)
    (eB : (B.poly N).map (Rat.castHom ℝ) = P.comp (Polynomial.X + Polynomial.C (o + b)))
    (eM : (M.poly N).map (Rat.castHom ℝ) = Q.comp (Polynomial.X + Polynomial.C (o + b)))
    (eR :
      (R.poly N).map (Rat.castHom ℝ) =
        (middleReflectionPoly P ((a : ℝ) + 1 / 2) b).comp (Polynomial.X + Polynomial.C o))
    (t : ℝ) :
    (((middleEulerCostRow N a p B M R).poly N).map (Rat.castHom ℝ)).eval t =
      (middleRatProfiles (a : ℝ) b (p : ℝ) P Q 0).eval (t + o) := by
  rw [middle_euler_cost_row_poly N a p B M R hB hM hR]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Rat.coe_castHom, eB, eM, eR,
    middleRatProfiles, Fin.cases_zero, middleRatEndpoint, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_X, Rat.cast_add,
    Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one]
  rw [← add_assoc]
  ring

/-- The second residual row is the translated conductor profile with the
rational factor arising from the direct Gaussian radius. -/
@[expose]
public def middleConductorCostRow (p : ℚ) (B : MiddleIntRow) : MiddleIntRow :=
  B.scaleRat (2 * p / (519674416 / 10 ^ 9))

/-- The integer conductor row represents the second residual profile at the
same local coordinate as the Euler row. -/
public theorem middle_conductor_row_eval (N : ℕ) (a p : ℚ) (b o : ℝ) (B : MiddleIntRow)
    (P Q : Polynomial ℝ)
    (eB : (B.poly N).map (Rat.castHom ℝ) = P.comp (Polynomial.X + Polynomial.C (o + b))) (t : ℝ) :
    (((middleConductorCostRow p B).poly N).map (Rat.castHom ℝ)).eval t =
      (middleRatProfiles (a : ℝ) b (p : ℝ) P Q 1).eval (t + o) := by
  have he :
    middleRatProfiles (a : ℝ) b (p : ℝ) P Q 1 =
      Polynomial.C (2 * (p : ℝ) / gaussianDirectScale) * P.comp (Polynomial.X + Polynomial.C b) :=
    rfl
  rw [middleConductorCostRow, MiddleIntRow.poly_scaleRat, he]
  simp only [Polynomial.map_mul, Polynomial.map_C, Rat.coe_castHom, eB, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Rat.cast_mul,
    Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, gaussianDirectScale, add_assoc]

end PseudoPrime.PrimeTestBounds.MillerRabin
