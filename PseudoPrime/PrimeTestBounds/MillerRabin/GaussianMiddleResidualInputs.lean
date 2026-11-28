/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleResidualRows

/-! # Integer input transforms for the middle residual -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A forward moment computed from a profile that has already been shifted
represents the unshifted moment evaluated in the same translated coordinates. -/
public theorem middle_shifted_moment_poly (B S : MiddleIntRow) (N : ℕ) (n d : ℤ) (z : ℚ)
    (hS : S.den ≠ 0) (hn : n ≠ 0) (hd : d ≠ 0) (hs : S.nums.size ≤ N + 1)
    (he : S.poly N = (B.poly N).comp (Polynomial.X + Polynomial.C z)) :
    (S.moment N n d).poly N =
      (middleMomentPoly (B.poly N) ((n : ℚ) / d) 0).comp (Polynomial.X + Polynomial.C z) := by
  rw [S.poly_moment N n d hS hn hs, he, ←
    middle_moment_translate _ (div_ne_zero (Int.cast_ne_zero.mpr hn) (Int.cast_ne_zero.mpr hd))]
  simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X]

/-- Build the source of the reflected moment after the common shift. -/
@[expose]
public def middleReflectionSource (N : ℕ) (σ : ℚ) (S : MiddleIntRow) : MiddleIntRow :=
  (S.scaleRat σ).add N (S.deriv N)

/-- The reflected source is the shifted profile multiplied by the Euler
exponent, plus its derivative. -/
public theorem middle_reflection_source_poly (N : ℕ) (σ : ℚ) (S : MiddleIntRow) (hS : 0 < S.den)
    (hs : S.nums.size ≤ N + 1) :
    (middleReflectionSource N σ S).poly N = Polynomial.C σ * S.poly N + (S.poly N).derivative := by
  have hd : (S.deriv N).den ≠ 0 := hS.ne'
  rw [middleReflectionSource, MiddleIntRow.poly_add _ _ _ (S.scaleRat_pos hS σ).ne' hd,
    MiddleIntRow.poly_scaleRat, MiddleIntRow.poly_deriv,
    S.poly_eq_of_size_le (hs.trans (Nat.le_succ (N + 1))) hs]

/-- Compute the reflected moment directly from the shifted source. The
offset (z) includes both the pole shift and the numerical coordinate origin. -/
public theorem middle_shifted_reflection_poly (B S : MiddleIntRow) (N : ℕ) (n d : ℤ) (z : ℚ)
    (hS : 0 < S.den) (hn : n ≠ 0) (hd : d ≠ 0) (hs : S.nums.size ≤ N + 1)
    (he : S.poly N = (B.poly N).comp (Polynomial.X + Polynomial.C z)) :
    let σ := ((n : ℚ) / d) + 1
    ((middleReflectionSource N σ S).moment N n d).poly N = middleReflectionPoly (B.poly N) σ z := by
  intro σ
  have hden : 0 < (middleReflectionSource N σ S).den := mul_pos (S.scaleRat_pos hS σ) hS
  have hsize : (middleReflectionSource N σ S).nums.size ≤ N + 1 := by
    simp only [middleReflectionSource, MiddleIntRow.add, Array.size_ofFn, le_refl]
  rw [MiddleIntRow.poly_moment _ _ _ _ hden.ne' hn hsize, middle_reflection_source_poly N σ S hS hs,
    he, middleReflectionPoly]
  have hr : σ - 1 = (n : ℚ) / d := add_sub_cancel_right _ _
  rw [hr,
    middle_moment_translate (Polynomial.C σ * B.poly N + (B.poly N).derivative)
      (div_ne_zero (Int.cast_ne_zero.mpr hn) (Int.cast_ne_zero.mpr hd)) z]
  congr 1
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.derivative_comp, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, one_mul]

/-- Construct both residual rows from one shifted physical profile.
The integer rates are `n / d` for the forward moment and `m / d` for reflection. -/
@[expose]
public def middleInputRows (B : MiddleIntRow) (N o : ℕ) (n m d : ℤ) (p : ℚ) :
    MiddleIntRow × MiddleIntRow :=
  let S := B.shift N (2 * (o : ℤ) + 7) 2
  let M := S.moment N n d
  let R := (middleReflectionSource N ((m : ℚ) / d + 1) S).moment N m d
  (middleEulerCostRow N ((m : ℚ) / d + 1 / 2) p S M R, middleConductorCostRow p S)

/-- Both residual rows have positive common denominators at positive rates. -/
public theorem middle_input_rows_pos (B : MiddleIntRow) (N o : ℕ) (n m d : ℤ) (p : ℚ)
    (hB : 0 < B.den) (hn : 0 < n) (hm : 0 < m) :
    0 < (middleInputRows B N o n m d p).1.den ∧ 0 < (middleInputRows B N o n m d p).2.den := by
  let S := B.shift N (2 * (o : ℤ) + 7) 2
  have hS : 0 < S.den := mul_pos hB (pow_pos (by decide : (0 : ℤ) < 2) _)
  have hR : 0 < (middleReflectionSource N ((m : ℚ) / d + 1) S).den :=
    mul_pos (S.scaleRat_pos hS _) hS
  refine
    ⟨middle_euler_row_den_pos _ _ _ hS (mul_pos hS (pow_pos hn _)) (mul_pos hR (pow_pos hm _)),
      S.scaleRat_pos hS _⟩

/-- Translating a reflected moment adds the offset to the pole shift. -/
private theorem middle_reflection_translate (P : Polynomial ℝ) (σ b o : ℝ) :
    middleReflectionPoly P σ (o + b) =
      (middleReflectionPoly P σ b).comp (Polynomial.X + Polynomial.C o) := by
  simp only [middleReflectionPoly, middleMomentPoly, Polynomial.comp_assoc, Polynomial.add_comp,
    Polynomial.X_comp, Polynomial.C_comp, add_assoc, Polynomial.C_add]

/-- Evaluate both computed rows as the analytic rational profiles at the
global coordinate. No coefficient identity is checked anew at an endpoint. -/
public theorem middle_input_rows_eval (B : MiddleIntRow) (N o : ℕ) (n m d : ℤ) (p : ℚ)
    (hB : 0 < B.den) (hn : 0 < n) (hm : 0 < m) (hd : d ≠ 0) (t : ℝ) :
    let P := (B.poly N).map (Rat.castHom ℝ)
    let Q := (middleMomentPoly (B.poly N) ((n : ℚ) / d) 0).map (Rat.castHom ℝ)
    let a := ((m : ℚ) / d + 1 / 2 : ℚ)
    let A := middleInputRows B N o n m d p
    let F := middleRatProfiles (a : ℝ) (7 / 2) (p : ℝ) P Q
    ((A.1.poly N).map (Rat.castHom ℝ)).eval t = (F 0).eval (t + o) ∧
      ((A.2.poly N).map (Rat.castHom ℝ)).eval t = (F 1).eval (t + o) := by
  intro P Q a A F
  let w : ℤ := 2 * (o : ℤ) + 7
  let z : ℚ := (w : ℚ) / 2
  let S := B.shift N w 2
  let M := S.moment N n d
  let R := (middleReflectionSource N ((m : ℚ) / d + 1) S).moment N m d
  have hz : (z : ℝ) = (o : ℝ) + 7 / 2 := by
    rw [show (z : ℝ) = (w : ℝ) / 2 by simp only [z, Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast]]
    simp only [w, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_ofNat]
    ring
  have hσ : (((m : ℚ) / d + 1 : ℚ) : ℝ) = (a : ℝ) + 1 / 2 := by
    simp only [a, Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_ofNat]
    ring
  have hS : 0 < S.den := mul_pos hB (pow_pos (by decide : (0 : ℤ) < 2) _)
  have hM : 0 < M.den := mul_pos hS (pow_pos hn _)
  have hR : 0 < R.den := mul_pos (mul_pos (S.scaleRat_pos hS _) hS) (pow_pos hm _)
  have hs : S.nums.size ≤ N + 1 := by
    simp only [S, MiddleIntRow.shift, MiddleIntRow.affine, gaussianAffineRatioRow,
      gaussianAffineIntRow, Array.size_ofFn, le_refl]
  have he : S.poly N = (B.poly N).comp (Polynomial.X + Polynomial.C z) :=
    B.poly_shift N w 2 hB.ne' (by decide)
  have eB :
    (S.poly N).map (Rat.castHom ℝ) = P.comp (Polynomial.X + Polynomial.C ((o : ℝ) + 7 / 2)) := by
    rw [he, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom, hz]
  have eM :
    (M.poly N).map (Rat.castHom ℝ) = Q.comp (Polynomial.X + Polynomial.C ((o : ℝ) + 7 / 2)) := by
    rw [middle_shifted_moment_poly B S N n d z hS.ne' hn.ne' hd hs he, Polynomial.map_comp,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom, hz]
  have eR :
    (R.poly N).map (Rat.castHom ℝ) =
      (middleReflectionPoly P ((a : ℝ) + 1 / 2) (7 / 2)).comp
        (Polynomial.X + Polynomial.C (o : ℝ)) := by
    rw [middle_shifted_reflection_poly B S N m d z hS hm.ne' hd hs he, middle_reflection_poly_map,
      hz, hσ, middle_reflection_translate]
  exact
    ⟨middle_euler_row_eval _ a p _ _ S M R P Q hS hM hR eB eM eR t,
      middle_conductor_row_eval _ a p _ _ S P Q eB t⟩

/-- A shared row evaluated at the local rational offset supplies the
upper polynomial value needed by an endpoint certificate. -/
public theorem middle_input_endpoint_le (A : MiddleIntRow) (N : ℕ) (u v : ℤ) (hd : 0 < A.den)
    (hv : 0 < v) {o : ℝ} {P : Polynomial ℝ}
    (he : ((A.poly N).map (Rat.castHom ℝ)).eval ((u : ℝ) / v) = P.eval ((u : ℝ) / v + o)) :
    P.eval ((u : ℝ) / v + o) ≤ ((A.evalInterval N u v).upper : ℝ) / A.den := by
  rw [← he]
  exact (A.eval_interval_contains N u v hd hv).2

end PseudoPrime.PrimeTestBounds.MillerRabin
