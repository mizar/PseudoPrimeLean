/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianReflectedAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianDirectCurvatureRat
import Mathlib.Algebra.Polynomial.Taylor
import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Laplace bound for the reflected middle-kernel Euler terms -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nonnegative reflected profile and derivative beyond the anchor,
the Abel envelope is a single exact Laplace moment. This supplies the
absolute reflection estimate for the early K141 and K156 profiles. -/
public theorem reflected_log_poly_moment (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ)
    {σ : ℝ} (hσ : 1 < σ) (z : ℝ) (hP : ∀ x, z ≤ x → 0 ≤ P.eval x)
    (hD : ∀ x, z ≤ x → 0 ≤ P.derivative.eval x) :
    let Q := (Polynomial.C σ * P + P.derivative).comp (Polynomial.X + Polynomial.C z)
    |∑' n : ℕ,
          ArithmeticFunction.vonMangoldt n * τ n * ((n : ℝ) ^ (-σ) * P.eval (z + Real.log n))| ≤
      6 *
        ∑ j ∈ Finset.range (Q.natDegree + 1),
          Q.coeff j * ((j.factorial : ℝ) / (σ - 1) ^ (j + 1)) := by
  intro Q
  refine (reflected_log_abel_bound τ hτ P hσ z).trans ?_
  rw [reflected_abel_log_coordinate]
  have he :
    (∫ v in Set.Ioi (0 : ℝ),
        6 * Real.exp (-(σ - 1) * v) * (σ * |P.eval (z + v)| + |P.derivative.eval (z + v)|)) =
      ∫ v in Set.Ioi (0 : ℝ),
        6 * ((Polynomial.C σ * P + P.derivative).eval (z + v) * Real.exp (-(σ - 1) * v)) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro v hv
    have hz : z ≤ z + v := le_add_of_nonneg_right (le_of_lt hv)
    dsimp only
    rw [abs_of_nonneg (hP _ hz), abs_of_nonneg (hD _ hz), Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C]
    ring
  rw [he, MeasureTheory.integral_const_mul, polynomial_laplace_tail _ z (sub_pos.mpr hσ)]

/-- An integer translation check certifies the sign of both the reflected
profile and its derivative on the tail. The check is shared by all derivatives. -/
public theorem middle_profile_sign_of_row (P : Polynomial ℚ) (N : ℕ) (b H : ℤ) (q : ℕ → ℤ)
    (hH : 0 < H) (hP : P.natDegree ≤ N) (hq : ∀ j ≤ N, (q j : ℚ) = (H : ℚ) * P.coeff j)
    (hs : ∀ i ≤ N, 0 ≤ (gaussianAffineIntRow N b 1 q)[i]?.getD 0) (j : ℕ) {t : ℝ}
    (ht : (b : ℝ) ≤ t) : 0 ≤ ((Polynomial.derivative^[j]) (P.map (Rat.castHom ℝ))).eval t := by
  let Q := P.comp (Polynomial.X + Polynomial.C (b : ℚ))
  have hdeg : Q.natDegree ≤ N := by
    have hA : (Polynomial.X + Polynomial.C (b : ℚ)).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le Polynomial.natDegree_X.le
        ((Polynomial.natDegree_C _).le.trans (Nat.zero_le 1))
    exact Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hP hA).trans_eq (Nat.mul_one N))
  have hsign : ∀ i, 0 ≤ Q.coeff i := by
    intro i
    by_cases hi : i ≤ N
    · have he := gaussian_affine_int_coeff P N b 1 H q hP hq hi
      simp only [Int.cast_one, Polynomial.C_1, one_mul] at he
      have h := (Int.cast_nonneg_iff (R := ℚ)).mpr (hs i hi)
      rw [he] at h
      exact nonneg_of_mul_nonneg_right h (Int.cast_pos.mpr hH)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt (Nat.lt_of_not_ge hi))]
  apply derivative_nonneg_of_shift _ _ j ht
  intro i
  have he :
    (P.map (Rat.castHom ℝ)).comp (Polynomial.X + Polynomial.C (b : ℝ)) = Q.map (Rat.castHom ℝ) := by
    simp only [Q, Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom, Rat.cast_intCast]
  rw [he, Polynomial.coeff_map, Rat.coe_castHom, Rat.cast_nonneg]
  exact hsign i

/-- A single executable array check supplies both sign hypotheses for the
reflection moment bound at any anchor beyond the checked translation. -/
public theorem middle_profile_signs {N : ℕ} {b H : ℤ} (q : ℕ → ℤ) (hH : 0 < H)
    (hs : (gaussianAffineIntRow N b 1 q).all (fun c ↦ decide (0 ≤ c)) = true) {z : ℝ}
    (hz : (b : ℝ) ≤ z) :
    let P := (gaussianIntProfile N H q).map (Rat.castHom ℝ)
    (∀ x, z ≤ x → 0 ≤ P.eval x) ∧ (∀ x, z ≤ x → 0 ≤ P.derivative.eval x) := by
  have hrow (i : ℕ) (hi : i ≤ N) : 0 ≤ (gaussianAffineIntRow N b 1 q)[i]?.getD 0 := by
    have hlt : i < (gaussianAffineIntRow N b 1 q).size := by
      simpa only [gaussianAffineIntRow, Array.size_ofFn] using Nat.lt_succ_of_le hi
    rw [Array.getElem?_eq_getElem hlt, Option.getD_some]
    exact of_decide_eq_true ((Array.all_eq_true.mp hs) i hlt)
  have h j {x : ℝ} (hx : z ≤ x) :=
    middle_profile_sign_of_row _ N b H q hH (gaussian_int_profile_degree N H q)
      (fun _ hi ↦ gaussian_int_profile_coeff N H q hH.ne' hi) hrow j (hz.trans hx)
  exact ⟨fun x hx ↦ h 0 hx, fun x hx ↦ h 1 hx⟩

/-- A checked sign row gives the scaled reflection bound at `z = b + ℓ`.
The prefactor carries the original kernel scale and exponential decay. -/
public theorem middle_reflection_le_moment {N : ℕ} {origin H : ℤ} (q : ℕ → ℤ) (hH : 0 < H)
    (hs : (gaussianAffineIntRow N origin 1 q).all (fun c ↦ decide (0 ≤ c)) = true) (τ : ℕ → ℝ)
    (hτ : ∀ n, |τ n| ≤ 3) {a b ℓ κ : ℝ} (ha : 1 / 2 < a) (hκ : 0 ≤ κ) (hz : (origin : ℝ) ≤ b + ℓ) :
    let P := (gaussianIntProfile N H q).map (Rat.castHom ℝ)
    let σ := a + 1 / 2
    let K := κ * Real.exp (-a * b - a * ℓ)
    let Q := (Polynomial.C σ * P + P.derivative).comp (Polynomial.X + Polynomial.C (b + ℓ))
    |K *
          (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n * τ n *
              ((n : ℝ) ^ (-σ) * P.eval (b + ℓ + Real.log n)))| ≤
      K *
        (6 *
          ∑ i ∈ Finset.range (Q.natDegree + 1),
            Q.coeff i * ((i.factorial : ℝ) / (σ - 1) ^ (i + 1))) := by
  intro P σ K Q
  have hσ : 1 < σ := by
    dsimp only [σ]; linarith only [ha]
  have hK : 0 ≤ K := mul_nonneg hκ (Real.exp_nonneg _)
  have h := middle_profile_signs q hH hs hz
  rw [abs_mul, abs_of_nonneg hK]
  exact mul_le_mul_of_nonneg_left (reflected_log_poly_moment τ hτ P hσ _ h.1 h.2) hK

/-- Integer coefficient of the square of a numerator row. -/
@[expose]
public def middleSquareCoeff (q : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (i + 1), q j * q (i - j)

/-- For a polynomial formed from a common-denominator row, the square
coefficient is the integer convolution divided by the squared denominator. -/
private theorem middle_square_coeff (N : ℕ) (D : ℤ) (q : ℕ → ℤ) (hD : D ≠ 0) {i : ℕ} (hi : i ≤ N) :
    ((gaussianIntProfile N D q) ^ 2).coeff i = (middleSquareCoeff q i : ℚ) / (D : ℚ) ^ 2 := by
  rw [pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun j k ↦ (gaussianIntProfile N D q).coeff j * (gaussianIntProfile N D q).coeff k)]
  simp only [middleSquareCoeff, Int.cast_sum, Finset.sum_div, Int.cast_mul, pow_two]
  apply Finset.sum_congr rfl
  intro j hj
  have hji := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hd : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have he (k : ℕ) (hk : k ≤ N) : (gaussianIntProfile N D q).coeff k = (q k : ℚ) / D := by
    apply (eq_div_iff hd).mpr
    rw [mul_comm, ← gaussian_int_profile_coeff N D q hD hk]
  rw [he j (hji.trans hi), he (i - j) ((Nat.sub_le i j).trans hi), div_mul_div_comm]

/-- The inverse-transform polynomial of the squared kernel coefficients.
Index reversal matches the pole order, and each monomial is divided by its factorial. -/
@[expose]
public noncomputable def middlePoleProfile (N : ℕ) (P : Polynomial ℚ) : Polynomial ℚ :=
  ∑ i ∈ Finset.range (N + 1), Polynomial.monomial i ((P ^ 2).coeff (N - i) / i.factorial)

/-- The cleared coefficient equalities identify a supplied reflection row with
the inverse transform of the original squared kernel polynomial. -/
public theorem middle_pole_profile_eq (N : ℕ) (D H : ℤ) (q v : ℕ → ℤ) (hD : D ≠ 0) (hH : H ≠ 0)
    (h : ∀ i ≤ N, v i * D ^ 2 * (i.factorial : ℤ) = H * middleSquareCoeff q (N - i)) :
    gaussianIntProfile N H v = middlePoleProfile N (gaussianIntProfile N D q) := by
  rw [gaussianIntProfile, middlePoleProfile]
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [middle_square_coeff N D q hD (Nat.sub_le _ _), div_div]
  apply congrArg (Polynomial.monomial i)
  have hd : (D : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hD
  have hh : (H : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hH
  have hf : (i.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  apply (div_eq_div_iff hh (mul_ne_zero (pow_ne_zero 2 hd) hf)).mpr
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast, mul_assoc, mul_comm (H : ℚ)] using
    congrArg (fun x : ℤ ↦ (x : ℚ)) (h i hin)

/-- The reflected term of the original squared kernel is bounded by the
Laplace moment of its inverse-transform polynomial, with both integer checks shared. -/
public theorem middle_pole_reflection_le {N : ℕ} {origin H D : ℤ} (q v : ℕ → ℤ) (hH : 0 < H)
    (hD : D ≠ 0) (he : ∀ i ≤ N, v i * D ^ 2 * (i.factorial : ℤ) = H * middleSquareCoeff q (N - i))
    (hs : (gaussianAffineIntRow N origin 1 v).all (fun c ↦ decide (0 ≤ c)) = true) (τ : ℕ → ℝ)
    (hτ : ∀ n, |τ n| ≤ 3) {a b ℓ κ : ℝ} (ha : 1 / 2 < a) (hκ : 0 ≤ κ) (hz : (origin : ℝ) ≤ b + ℓ) :
    let P := (middlePoleProfile N (gaussianIntProfile N D q)).map (Rat.castHom ℝ)
    let σ := a + 1 / 2
    let K := κ * Real.exp (-a * b - a * ℓ)
    let Q := (Polynomial.C σ * P + P.derivative).comp (Polynomial.X + Polynomial.C (b + ℓ))
    |K *
          (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n * τ n *
              ((n : ℝ) ^ (-σ) * P.eval (b + ℓ + Real.log n)))| ≤
      K *
        (6 *
          ∑ i ∈ Finset.range (Q.natDegree + 1),
            Q.coeff i * ((i.factorial : ℝ) / (σ - 1) ^ (i + 1))) := by
  have h := middle_reflection_le_moment v hH hs τ hτ ha hκ hz
  rw [middle_pole_profile_eq N D H q v hD hH.ne' he] at h
  exact h

/-- The translated Laplace moment as a polynomial in the cutoff logarithm.
Hasse derivatives give its coefficients without repeating translations at endpoints. -/
@[expose]
public noncomputable def middleMomentPoly {R : Type*} [Field R] (P : Polynomial R) (r b : R) :
    Polynomial R :=
  (∑ i ∈ Finset.range (P.natDegree + 1),
        Polynomial.hasseDeriv i P * Polynomial.C ((i.factorial : R) / r ^ (i + 1))).comp
    (Polynomial.X + Polynomial.C b)

/-- The reflection envelope is the translated Laplace moment of the sum of
the rate-weighted profile and its derivative. -/
@[expose]
public noncomputable def middleReflectionPoly {R : Type*} [Field R] (P : Polynomial R) (σ b : R) :
    Polynomial R :=
  middleMomentPoly (Polynomial.C σ * P + P.derivative) (σ - 1) b

/-- The reflection polynomial evaluates to the translated Laplace moment. -/
public theorem middle_reflection_poly_eval (P : Polynomial ℝ) (σ b ℓ : ℝ) :
    let U := Polynomial.C σ * P + P.derivative
    let Q := U.comp (Polynomial.X + Polynomial.C (b + ℓ))
    (middleReflectionPoly P σ b).eval ℓ =
      ∑ i ∈ Finset.range (Q.natDegree + 1),
        Q.coeff i * ((i.factorial : ℝ) / (σ - 1) ^ (i + 1)) := by
  intro U Q
  have hQ : Q = Polynomial.taylor (b + ℓ) U := (Polynomial.taylor_apply _ _).symm
  rw [hQ, middleReflectionPoly, middleMomentPoly, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, add_comm ℓ b]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.natDegree_taylor, Polynomial.taylor_coeff, U]

/-- The reflected contribution to the middle residual is bounded by its
polynomial envelope times the original exponential decay. -/
public theorem middle_reflection_le_poly (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ)
    {a b ℓ κ : ℝ} (ha : 1 / 2 < a) (hκ : 0 ≤ κ) (hP : ∀ x, b + ℓ ≤ x → 0 ≤ P.eval x)
    (hD : ∀ x, b + ℓ ≤ x → 0 ≤ P.derivative.eval x) :
    let σ := a + 1 / 2
    let K := κ * Real.exp (-a * b - a * ℓ)
    |K *
          (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n * τ n *
              ((n : ℝ) ^ (-σ) * P.eval (b + ℓ + Real.log n)))| ≤
      K * (6 * (middleReflectionPoly P σ b).eval ℓ) := by
  intro σ K
  have hs : 1 < σ := by
    dsimp only [σ]; linarith only [ha]
  have hK : 0 ≤ K := mul_nonneg hκ (Real.exp_nonneg _)
  rw [abs_mul, abs_of_nonneg hK, middle_reflection_poly_eval]
  exact mul_le_mul_of_nonneg_left (reflected_log_poly_moment τ hτ P hs _ hP hD) hK

/-- Coercion preserves the rational reflection polynomial, so its coefficients
can be assembled before any real comparison is made. -/
public theorem middle_reflection_poly_map (P : Polynomial ℚ) (σ b : ℚ) :
    (middleReflectionPoly P σ b).map (Rat.castHom ℝ) =
      middleReflectionPoly (P.map (Rat.castHom ℝ)) (σ : ℝ) (b : ℝ) := by
  have hU :
    (Polynomial.C σ * P + P.derivative).map (Rat.castHom ℝ) =
      Polynomial.C (σ : ℝ) * P.map (Rat.castHom ℝ) + (P.map (Rat.castHom ℝ)).derivative := by
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.derivative_map,
      Rat.coe_castHom]
  have hdeg :=
    Polynomial.natDegree_map_eq_of_injective (f := Rat.castHom ℝ) (Rat.cast_injective (α := ℝ))
      (p := Polynomial.C σ * P + P.derivative)
  rw [hU] at hdeg
  simp only [middleReflectionPoly, middleMomentPoly, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C, Rat.coe_castHom, Polynomial.map_sum, Polynomial.map_mul,
    ← Polynomial.hasseDeriv_map, hU, hdeg, Rat.cast_div, Rat.cast_natCast, Rat.cast_pow,
    Rat.cast_sub, Rat.cast_one]

/-- The reflection moment is nonnegative when the profile and its derivative
are nonnegative beyond the cutoff. -/
public theorem middle_reflection_poly_nonneg (P : Polynomial ℝ) {σ b ℓ : ℝ} (hσ : 1 < σ)
    (hP : ∀ x, b + ℓ ≤ x → 0 ≤ P.eval x) (hD : ∀ x, b + ℓ ≤ x → 0 ≤ P.derivative.eval x) :
    0 ≤ (middleReflectionPoly P σ b).eval ℓ := by
  rw [middle_reflection_poly_eval]
  rw [← polynomial_laplace_tail (Polynomial.C σ * P + P.derivative) (b + ℓ) (sub_pos.mpr hσ)]
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have h : b + ℓ ≤ b + ℓ + t := le_add_of_nonneg_right (Set.mem_Ioi.mp ht).le
  rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  exact
    mul_nonneg (add_nonneg (mul_nonneg (zero_le_one.trans hσ.le) (hP _ h)) (hD _ h))
      (Real.exp_nonneg _)

/-- The certified rational prefactor can replace the exact normalization in
the reflected term of the middle residual, preserving the paper's decay factor. -/
public theorem middle_reflection_le_scaled_poly (τ : ℕ → ℝ) (hτ : ∀ n, |τ n| ≤ 3) (P : Polynomial ℝ)
    {a b ℓ κ p : ℝ} (ha : 1 / 2 < a) (hκ : 0 ≤ κ) (hp : κ * Real.exp (-a * b) ≤ p)
    (hP : ∀ x, b + ℓ ≤ x → 0 ≤ P.eval x) (hD : ∀ x, b + ℓ ≤ x → 0 ≤ P.derivative.eval x) :
    let σ := a + 1 / 2
    let K := κ * Real.exp (-a * b - a * ℓ)
    |K *
          (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n * τ n *
              ((n : ℝ) ^ (-σ) * P.eval (b + ℓ + Real.log n)))| ≤
      Real.exp (-a * ℓ) * (6 * p * (middleReflectionPoly P σ b).eval ℓ) := by
  intro σ K
  have hσ : 1 < σ := by
    dsimp only [σ]; linarith only [ha]
  have hM := middle_reflection_poly_nonneg P hσ hP hD
  refine (middle_reflection_le_poly τ hτ P ha hκ hP hD).trans ?_
  have hK : K ≤ p * Real.exp (-a * ℓ) := by
    dsimp only [K]
    rw [sub_eq_add_neg, Real.exp_add, ← mul_assoc, ← neg_mul a ℓ]
    exact mul_le_mul_of_nonneg_right hp (Real.exp_nonneg _)
  calc
    _ ≤ (p * Real.exp (-a * ℓ)) * (6 * (middleReflectionPoly P σ b).eval ℓ) :=
      mul_le_mul_of_nonneg_right hK (mul_nonneg (by norm_num only) hM)
    _ = _ := by ring

/-- The original squared kernel uses the same rational reflection cap after
the coefficient and sign checks for its inverse-transform row. -/
public theorem middle_pole_reflection_le_scaled {N : ℕ} {origin H D : ℤ} (q v : ℕ → ℤ) (hH : 0 < H)
    (hD : D ≠ 0) (he : ∀ i ≤ N, v i * D ^ 2 * (i.factorial : ℤ) = H * middleSquareCoeff q (N - i))
    (hs : (gaussianAffineIntRow N origin 1 v).all (fun c ↦ decide (0 ≤ c)) = true) (τ : ℕ → ℝ)
    (hτ : ∀ n, |τ n| ≤ 3) {a b ℓ κ p : ℝ} (ha : 1 / 2 < a) (hκ : 0 ≤ κ)
    (hp : κ * Real.exp (-a * b) ≤ p) (hz : (origin : ℝ) ≤ b + ℓ) :
    let P := (middlePoleProfile N (gaussianIntProfile N D q)).map (Rat.castHom ℝ)
    let σ := a + 1 / 2
    let K := κ * Real.exp (-a * b - a * ℓ)
    |K *
          (∑' n : ℕ,
            ArithmeticFunction.vonMangoldt n * τ n *
              ((n : ℝ) ^ (-σ) * P.eval (b + ℓ + Real.log n)))| ≤
      Real.exp (-a * ℓ) * (6 * p * (middleReflectionPoly P σ b).eval ℓ) := by
  have h := middle_profile_signs v hH hs hz
  rw [middle_pole_profile_eq N D H q v hD hH.ne' he] at h
  exact middle_reflection_le_scaled_poly τ hτ _ ha hκ hp h.1 h.2

/-- Compute one Laplace-moment coefficient from a bounded rational power row.
The input row is zero beyond the polynomial degree. -/
@[expose]
public def middleMomentCoeff (N : ℕ) (r : ℚ) (q : ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (N + 1),
    (Nat.fast_choose (i + j) j : ℚ) * q (i + j) * ((j.factorial : ℚ) / r ^ (j + 1))

/-- The finite rational coefficient calculation agrees with the unshifted
Laplace polynomial. Extra zero terms permit one degree bound for all rows. -/
public theorem middle_moment_coeff_eq (P : Polynomial ℚ) (N : ℕ) (r : ℚ) (q : ℕ → ℚ)
    (hP : P.natDegree ≤ N) (hq : ∀ i, q i = P.coeff i) (i : ℕ) :
    middleMomentCoeff N r q i = (middleMomentPoly P r 0).coeff i := by
  simp only [middleMomentCoeff, middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X,
    Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C, Polynomial.hasseDeriv_coeff, hq,
    ← Nat.choose_eq_fast_choose]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hP))
  intro j _ hj
  have hj' := Nat.lt_of_not_ge (fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
  have hzero :=
    Polynomial.coeff_eq_zero_of_natDegree_lt
      (hj'.trans_le (Nat.le_add_left j i) : P.natDegree < i + j)
  simp only [hzero, zero_mul, mul_zero]

/-- The unshifted Laplace construction cannot increase degree. -/
public theorem middle_moment_degree (P : Polynomial ℚ) (r : ℚ) :
    (middleMomentPoly P r 0).natDegree ≤ P.natDegree := by
  simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact
    (Polynomial.natDegree_mul_C_le _ _).trans
      ((Polynomial.natDegree_hasseDeriv_le P j).trans (Nat.sub_le _ _))

/-- The executable row computes the Laplace transform once, then translates
it once for the common cutoff offset. -/
@[expose]
public def middleMomentRow (N : ℕ) (r b : ℚ) (q : ℕ → ℚ) : Array ℚ :=
  let row := Array.ofFn (fun i : Fin (N + 1) ↦ middleMomentCoeff N r q i.val)
  gaussianShiftRatRow N b (fun i ↦ row[i]?.getD 0)

/-- The two shared coefficient transformations give the exact cutoff moment. -/
public theorem middle_moment_row_eq (P : Polynomial ℚ) (N : ℕ) (r b : ℚ) (q : ℕ → ℚ)
    (hP : P.natDegree ≤ N) (hq : ∀ i, q i = P.coeff i) {i : ℕ} (hi : i ≤ N) :
    (middleMomentRow N r b q)[i]?.getD 0 = (middleMomentPoly P r b).coeff i := by
  have hq' (j : ℕ) (hj : j ≤ N) :
    (Array.ofFn (fun k : Fin (N + 1) ↦ middleMomentCoeff N r q k.val))[j]?.getD 0 =
      (middleMomentPoly P r 0).coeff j := by
    simpa only [Array.getElem?_ofFn, dite_eq_left (Nat.lt_succ_of_le hj), Option.getD_some] using
      middle_moment_coeff_eq P N r q hP hq j
  have he :=
    gaussian_shift_rat_coeff (middleMomentPoly P r 0) N b _ ((middle_moment_degree P r).trans hP)
      hq' hi
  simpa only [middleMomentRow, middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X] using
    he

/-- Clear all powers of the positive Laplace-rate numerator before forming
one coefficient. The original source denominator is kept separately. -/
@[expose]
public def middleMomentIntCoeff (N : ℕ) (a b : ℤ) (q : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (N + 1),
    (Nat.fast_choose (i + j) j : ℤ) * q (i + j) * ((j.factorial : ℤ) * b ^ (j + 1) * a ^ (N - j))

/-- The integer Laplace coefficient divided by its common denominator
equals the analytic Laplace polynomial coefficient. -/
public theorem middle_moment_int_coeff_eq (P : Polynomial ℚ) (N : ℕ) (a b H : ℤ) (q : ℕ → ℤ)
    (ha : a ≠ 0) (hH : H ≠ 0) (hP : P.natDegree ≤ N) (hq : ∀ i, (q i : ℚ) = (H : ℚ) * P.coeff i)
    (i : ℕ) :
    (middleMomentIntCoeff N a b q i : ℚ) / ((H : ℚ) * (a : ℚ) ^ (N + 1)) =
      (middleMomentPoly P ((a : ℚ) / b) 0).coeff i := by
  have har : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hHr : (H : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hH
  rw [← middle_moment_coeff_eq P N ((a : ℚ) / b) P.coeff hP (fun _ ↦ rfl) i]
  simp only [middleMomentIntCoeff, middleMomentCoeff, Int.cast_sum, Finset.sum_div, Int.cast_mul,
    Int.cast_natCast, Int.cast_pow, hq]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hpow : (a : ℚ) ^ (N + 1) = (a : ℚ) ^ (N - j) * (a : ℚ) ^ (j + 1) := by
    rw [← pow_add, ← Nat.add_assoc, Nat.sub_add_cancel hj']
  rw [div_pow, div_div_eq_mul_div, hpow]
  let c := ((Nat.fast_choose (i + j) j : ℚ) * P.coeff (i + j))
  calc
    _ =
        (((H : ℚ) * (a : ℚ) ^ (N - j)) * (c * ((j.factorial : ℚ) * (b : ℚ) ^ (j + 1)))) /
          (((H : ℚ) * (a : ℚ) ^ (N - j)) * (a : ℚ) ^ (j + 1)) :=
      by
      dsimp only [c]
      congr 1 <;> ring
    _ = _ := by rw [mul_div_mul_left _ _ (mul_ne_zero hHr (pow_ne_zero _ har)), mul_div_assoc]

/-- Compute the integer Laplace row with shared rate powers and factorials. -/
@[expose]
public def middleMomentIntRow (N : ℕ) (a b : ℤ) (q : ℕ → ℤ) : Array ℤ :=
  let weights :=
    Array.ofFn fun j : Fin (N + 1) ↦ (j.val.factorial : ℤ) * b ^ (j.val + 1) * a ^ (N - j.val)
  Array.ofFn fun i : Fin (N + 1) ↦
    ∑ j ∈ Finset.range (N + 1),
      (Nat.fast_choose (i.val + j) j : ℤ) * q (i.val + j) * weights[j]?.getD 0

/-- The cached moment row has the same coefficients as the scalar formula. -/
public theorem middle_moment_int_row_eq (N : ℕ) (a b : ℤ) (q : ℕ → ℤ) {i : ℕ} (hi : i ≤ N) :
    (middleMomentIntRow N a b q)[i]?.getD 0 = middleMomentIntCoeff N a b q i := by
  simp only [middleMomentIntRow, middleMomentIntCoeff, Array.getElem?_ofFn,
    dite_eq_left (Nat.lt_succ_of_le hi), Option.getD_some]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dite_eq_left (Finset.mem_range.mp hj), Option.getD_some]

end PseudoPrime.PrimeTestBounds.MillerRabin
