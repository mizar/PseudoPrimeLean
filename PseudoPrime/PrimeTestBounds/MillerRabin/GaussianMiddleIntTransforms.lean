/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleIntRow
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddleReflection

/-! # Integer translation and Laplace transforms for Gaussian middle profiles -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- When the degree bound contains all source entries, zero padding agrees
with the coefficients of the row polynomial at every index. -/
public theorem MiddleIntRow.poly_coeff_all (r : MiddleIntRow) (N : ℕ) (hs : r.nums.size ≤ N + 1)
    (i : ℕ) : (r.poly N).coeff i = (r.num i : ℚ) / r.den := by
  by_cases hi : i ≤ N
  · exact r.poly_coeff hi
  · have h := Nat.succ_le_of_lt (Nat.lt_of_not_ge hi)
    have hr : r.nums[i]? = none := Array.getElem?_eq_none (hs.trans h)
    simp only [MiddleIntRow.poly, Polynomial.ofFn_coeff_eq_zero_of_ge _ h, MiddleIntRow.num, hr,
      Option.getD_none, Int.cast_zero, zero_div]

/-- Evaluate an integer row at a rational point with directed Horner rounding.
The result uses the input row's denominator as its scale. -/
@[expose]
public def MiddleIntRow.evalInterval (r : MiddleIntRow) (N : ℕ) (a b : ℤ) :
    Analysis.IntegerInterval :=
  gaussianRowHorner (N + 1) a b (Array.ofFn fun i : Fin (N + 1) ↦ ⟨r.num i.val, r.num i.val⟩)

/-- Horner evaluation encloses the corresponding real polynomial at the
rational endpoint without computing a translated coefficient row. -/
public theorem MiddleIntRow.eval_interval_contains (r : MiddleIntRow) (N : ℕ) (a b : ℤ)
    (hr : 0 < r.den) (hb : 0 < b) :
    (r.evalInterval N a b).Contains r.den
      (((r.poly N).map (Rat.castHom ℝ)).eval ((a : ℝ) / b)) := by
  apply gaussian_row_horner_contains hr hb
  · rw [Polynomial.natDegree_map_eq_of_injective (Rat.castHom ℝ).injective]
    exact Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _
  · intro i
    rw [Polynomial.coeff_map, Rat.coe_castHom]
    by_cases hi : i < N + 1
    · simp only [Array.getElem?_ofFn, dite_eq_left hi, Option.getD_some,
        r.poly_coeff (Nat.le_of_lt_succ hi), Rat.cast_div, Rat.cast_intCast,
        Analysis.IntegerInterval.Contains, le_refl, and_self]
    · simp only [Array.getElem?_ofFn, dite_eq_right hi, Option.getD_none, poly,
        Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hi), Rat.cast_zero,
        Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div, le_refl, and_self]

/-- Evaluate the first derivative directly from its integer coefficient row. -/
public theorem MiddleIntRow.deriv_interval_contains (r : MiddleIntRow) (N : ℕ) (a b : ℤ)
    (hr : 0 < r.den) (hb : 0 < b) :
    ((r.deriv N).evalInterval N a b).Contains r.den
      (((r.poly (N + 1)).map (Rat.castHom ℝ)).derivative.eval ((a : ℝ) / b)) := by
  have h := (r.deriv N).eval_interval_contains N a b hr hb
  rw [r.poly_deriv N, ← Polynomial.derivative_map] at h
  exact h

/-- Apply the affine substitution `(w / b) * X + a / b` with one denominator. -/
@[expose]
public def MiddleIntRow.affine (r : MiddleIntRow) (N : ℕ) (a w b : ℤ) : MiddleIntRow :=
  ⟨r.den * b ^ N, gaussianAffineRatioRow N a w b r.num⟩

/-- The integer affine row represents the corresponding substitution. -/
public theorem MiddleIntRow.poly_affine (r : MiddleIntRow) (N : ℕ) (a w b : ℤ) (hr : r.den ≠ 0)
    (hb : b ≠ 0) :
    (r.affine N a w b).poly N =
      (r.poly N).comp (Polynomial.C ((w : ℚ) / b) * Polynomial.X + Polynomial.C ((a : ℚ) / b)) := by
  have hP : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hc : (r.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hq (i : ℕ) (hi : i ≤ N) : (r.num i : ℚ) = (r.den : ℚ) * (r.poly N).coeff i := by
    rw [r.poly_coeff hi, ← mul_div_assoc, mul_comm (r.den : ℚ), mul_div_cancel_right₀ _ hc]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ N
  · have he := gaussian_affine_ratio_coeff (r.poly N) N a w b r.den r.num hb hP hq hi
    have hbr : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
    rw [MiddleIntRow.poly_coeff _ hi]
    simp only [MiddleIntRow.affine, MiddleIntRow.num, Int.cast_mul, Int.cast_pow] at *
    rw [he, mul_comm, mul_div_cancel_right₀ _ (mul_ne_zero hc (pow_ne_zero _ hbr))]
  · have hA :
      (Polynomial.C ((w : ℚ) / b) * Polynomial.X + Polynomial.C ((a : ℚ) / b)).natDegree ≤ 1 :=
      Polynomial.natDegree_add_le_of_degree_le
        (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (Polynomial.natDegree_C _).le Polynomial.natDegree_X.le))
        ((Polynomial.natDegree_C _).le.trans (Nat.zero_le 1))
    have hd := Polynomial.natDegree_comp_le.trans ((Nat.mul_le_mul hP hA).trans_eq (Nat.mul_one N))
    have h := Nat.lt_of_not_ge hi
    exact
      (Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt h)).trans
        (Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt h)).symm

/-- Translate by `a / b` with a single shared denominator. -/
@[expose]
public def MiddleIntRow.shift (r : MiddleIntRow) (N : ℕ) (a b : ℤ) : MiddleIntRow :=
  r.affine N a b b

/-- The integer shift represents translation of the rational polynomial. -/
public theorem MiddleIntRow.poly_shift (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0)
    (hb : b ≠ 0) :
    (r.shift N a b).poly N = (r.poly N).comp (Polynomial.X + Polynomial.C ((a : ℚ) / b)) := by
  simpa only [MiddleIntRow.shift, div_self (Int.cast_ne_zero.mpr hb : (b : ℚ) ≠ 0), Polynomial.C_1,
    one_mul] using r.poly_affine N a b b hr hb

/-- Compute the unshifted Laplace row at rate `a / b`. -/
@[expose]
public def MiddleIntRow.moment (r : MiddleIntRow) (N : ℕ) (a b : ℤ) : MiddleIntRow :=
  ⟨r.den * a ^ (N + 1), middleMomentIntRow N a b r.num⟩

/-- A bounded source row is transformed into the corresponding Laplace polynomial. -/
public theorem MiddleIntRow.poly_moment (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0)
    (ha : a ≠ 0) (hs : r.nums.size ≤ N + 1) :
    (r.moment N a b).poly N = middleMomentPoly (r.poly N) ((a : ℚ) / b) 0 := by
  have hP : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hc : (r.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hq (i : ℕ) : (r.num i : ℚ) = (r.den : ℚ) * (r.poly N).coeff i := by
    rw [r.poly_coeff_all N hs i, ← mul_div_assoc, mul_comm (r.den : ℚ), mul_div_cancel_right₀ _ hc]
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  by_cases hi : i ≤ N
  · rw [MiddleIntRow.poly_coeff _ hi]
    simp only [MiddleIntRow.moment, MiddleIntRow.num, Int.cast_mul, Int.cast_pow,
      middle_moment_int_row_eq N a b r.num hi]
    exact middle_moment_int_coeff_eq (r.poly N) N a b r.den r.num ha hr hP hq i
  · have hd := (middle_moment_degree (r.poly N) ((a : ℚ) / b)).trans hP
    have h := Nat.lt_of_not_ge hi
    exact
      (Polynomial.ofFn_coeff_eq_zero_of_ge _ (Nat.succ_le_of_lt h)).trans
        (Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt h)).symm

/-- The two integer transforms represent the Laplace polynomial at the
common cutoff offset `u / v`. -/
public theorem MiddleIntRow.poly_moment_shift (r : MiddleIntRow) (N : ℕ) (a b u v : ℤ)
    (hr : r.den ≠ 0) (ha : a ≠ 0) (hv : v ≠ 0) (hs : r.nums.size ≤ N + 1) :
    ((r.moment N a b).shift N u v).poly N =
      middleMomentPoly (r.poly N) ((a : ℚ) / b) ((u : ℚ) / v) := by
  have hden : (r.moment N a b).den ≠ 0 := mul_ne_zero hr (pow_ne_zero _ ha)
  rw [MiddleIntRow.poly_shift _ _ _ _ hden hv, r.poly_moment N a b hr ha hs]
  simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X]

/-- Enlarging a degree bound past the stored row adds only zero coefficients. -/
public theorem MiddleIntRow.poly_eq_of_size_le (r : MiddleIntRow) {N M : ℕ}
    (hN : r.nums.size ≤ N + 1) (hM : r.nums.size ≤ M + 1) : r.poly N = r.poly M := by
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  rw [r.poly_coeff_all N hN, r.poly_coeff_all M hM]

/-- The polynomial Laplace equation at a nonzero rate determines its solution uniquely. -/
public theorem middle_moment_unique {r : ℚ} (hr : r ≠ 0) (P Q : Polynomial ℚ)
    (h : Polynomial.C r * P - P.derivative = Polynomial.C r * Q - Q.derivative) : P = Q := by
  apply sub_eq_zero.mp
  by_contra hne
  have he : Polynomial.C r * (P - Q) = (P - Q).derivative := by
    rw [mul_sub, Polynomial.derivative_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h
  have hc := congrArg (fun R : Polynomial ℚ => R.coeff (P - Q).natDegree) he
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), zero_mul] at hc
  exact (mul_ne_zero hr (Polynomial.leadingCoeff_ne_zero.mpr hne)) hc

private theorem moment_summand (P : Polynomial ℚ) (r : ℚ) (i : ℕ) :
    Polynomial.hasseDeriv i P * Polynomial.C ((i.factorial : ℚ) / r ^ (i + 1)) =
      Polynomial.derivative^[i] P * Polynomial.C (1 / r ^ (i + 1)) := by
  rw [← Polynomial.factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul, ←
    Polynomial.C_eq_natCast, mul_comm (Polynomial.C (i.factorial : ℚ)) (Polynomial.hasseDeriv i P),
    mul_assoc, ← map_mul, mul_one_div]

/-- The unshifted Laplace polynomial solves the first-order equation for its source. -/
public theorem middle_moment_ode (P : Polynomial ℚ) {r : ℚ} (hr : r ≠ 0) :
    Polynomial.C r * middleMomentPoly P r 0 - (middleMomentPoly P r 0).derivative = P := by
  simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X, moment_summand,
    Finset.mul_sum, Polynomial.derivative_sum]
  let f := fun i : ℕ => Polynomial.derivative^[i] P * Polynomial.C (1 / r ^ i)
  have hmain (i : ℕ) :
    Polynomial.C r * (Polynomial.derivative^[i] P * Polynomial.C (1 / r ^ (i + 1))) = f i := by
    rw [mul_left_comm, ← map_mul, pow_succ, one_div, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hr,
      one_mul, ← one_div]
  have hder (i : ℕ) :
    (Polynomial.derivative^[i] P * Polynomial.C (1 / r ^ (i + 1))).derivative = f (i + 1) := by
    rw [Polynomial.derivative_mul, Polynomial.derivative_C, mul_zero, add_zero]
    exact
      congrArg (fun Q : Polynomial ℚ => Q * Polynomial.C (1 / r ^ (i + 1)))
        (Function.iterate_succ_apply' Polynomial.derivative i P).symm
  simp only [hmain, hder]
  have hlast : f (P.natDegree + 1) = 0 := by
    simp only [f, Polynomial.iterate_derivative_eq_zero (Nat.lt_succ_self P.natDegree), zero_mul]
  have hzero : f 0 = P := by
    simp only [f, Function.iterate_zero, id_eq, pow_zero, div_one, Polynomial.C_1, mul_one]
  rw [Finset.sum_range_succ' f, Finset.sum_range_succ (fun i => f (i + 1)), hlast, add_zero, hzero,
    add_sub_cancel_left]

/-- A candidate satisfying the polynomial Laplace equation is the unshifted moment. -/
public theorem middle_moment_eq_of_ode {r : ℚ} (hr : r ≠ 0) {P M : Polynomial ℚ}
    (h : Polynomial.C r * M - M.derivative = P) : M = middleMomentPoly P r 0 := by
  exact middle_moment_unique hr _ _ (h.trans (middle_moment_ode P hr).symm)

/-- Translating the Laplace moment is equivalent to translating its source. -/
public theorem middle_moment_translate (P : Polynomial ℚ) {r : ℚ} (hr : r ≠ 0) (z : ℚ) :
    middleMomentPoly P r z = middleMomentPoly (P.comp (Polynomial.X + Polynomial.C z)) r 0 := by
  let Q := Polynomial.X + Polynomial.C z
  have h : middleMomentPoly P r z = (middleMomentPoly P r 0).comp Q := by
    simp only [middleMomentPoly, Polynomial.C_0, add_zero, Polynomial.comp_X, Q]
  rw [h]
  apply middle_moment_eq_of_ode hr
  simpa only [Polynomial.sub_comp, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.derivative_comp, Q, Polynomial.derivative_add, Polynomial.derivative_X,
    Polynomial.derivative_C, add_zero, one_mul, mul_one] using
    congrArg (fun M : Polynomial ℚ ↦ M.comp Q) (middle_moment_ode P hr)

/-- The constant of a Laplace moment needs just one integer coefficient sum. -/
public theorem MiddleIntRow.moment_head (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0)
    (ha : a ≠ 0) (hs : r.nums.size ≤ N + 1) :
    (middleMomentPoly (r.poly N) ((a : ℚ) / b) 0).eval 0 =
      (middleMomentIntCoeff N a b r.num 0 : ℚ) / ((r.den : ℚ) * (a : ℚ) ^ (N + 1)) := by
  have hd : (r.poly N).natDegree ≤ N :=
    Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
  have hq (i : ℕ) : (r.num i : ℚ) = (r.den : ℚ) * (r.poly N).coeff i := by
    rw [r.poly_coeff_all N hs i, ← mul_div_assoc, mul_comm (r.den : ℚ),
      mul_div_cancel_right₀ _ (Int.cast_ne_zero.mpr hr)]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact (middle_moment_int_coeff_eq (r.poly N) N a b r.den r.num ha hr hd hq 0).symm

/-- Coefficient recurrences identify a candidate with the unshifted Laplace moment. -/
public theorem middle_moment_eq_of_coeff {r : ℚ} (hr : r ≠ 0) {P M : Polynomial ℚ}
    (h : ∀ i : ℕ, r * M.coeff i - M.coeff (i + 1) * (i + 1 : ℕ) = P.coeff i) :
    M = middleMomentPoly P r 0 := by
  apply middle_moment_eq_of_ode hr
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro i
  simpa only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    Nat.cast_add, Nat.cast_one] using h i

/-- Check the coefficient row of the twice-reflected derivative by integer
cross-products. The source rate is `a/b`. -/
@[expose]
public def MiddleIntRow.secondMatches (N : ℕ) (a b : ℤ) (p q : MiddleIntRow) : Bool :=
  (List.range (N + 1)).all
    (fun i ↦
      decide
        (p.den * b ^ 2 * q.num i =
          q.den *
            (a ^ 2 * p.num i - 2 * a * b * (i + 1 : ℕ) * p.num (i + 1) +
              b ^ 2 * (i + 1 : ℕ) * (i + 2 : ℕ) * p.num (i + 2))))

/-- The checked target row is the twice-reflected derivative of the source
polynomial. The coefficient identity is independent of the eventual partitions. -/
public theorem MiddleIntRow.poly_of_secondMatches {N : ℕ} {a b : ℤ} {p q : MiddleIntRow}
    (hb : b ≠ 0) (hp : p.den ≠ 0) (hq : q.den ≠ 0) (hs : p.nums.size ≤ N + 1)
    (ht : q.nums.size ≤ N + 1) (h : p.secondMatches N a b q = true) :
    let d := (a : ℚ) / b
    q.poly N =
      Polynomial.C (d ^ 2) * p.poly N - Polynomial.C (2 * d) * (p.poly N).derivative +
        (p.poly N).derivative.derivative := by
  intro d
  ext i
  simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_derivative]
  by_cases hi : i ≤ N
  · have he :=
      of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr (Nat.lt_succ_of_le hi)))
    have hr := congrArg (fun x : ℤ ↦ (x : ℚ)) he
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_add, Int.cast_pow, Int.cast_natCast,
      Int.cast_ofNat, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hr
    rw [q.poly_coeff_all N ht, p.poly_coeff_all N hs, p.poly_coeff_all N hs, p.poly_coeff_all N hs]
    dsimp only [d]
    field_simp (disch :=
      first
      | exact Int.cast_ne_zero.mpr hb
      | exact Int.cast_ne_zero.mpr hp
      | exact Int.cast_ne_zero.mpr hq)
    norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hr ⊢
    linear_combination hr
  · have hN (r : MiddleIntRow) : (r.poly N).natDegree ≤ N :=
      Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
    have hn := Nat.lt_of_not_ge hi
    have h0 := Polynomial.coeff_eq_zero_of_natDegree_lt ((hN p).trans_lt hn)
    have h1 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hN p).trans_lt (hn.trans (Nat.lt_succ_self i)))
    have h2 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((hN p).trans_lt (hn.trans ((Nat.lt_succ_self i).trans (Nat.lt_succ_self (i + 1)))))
    simp only [Polynomial.coeff_eq_zero_of_natDegree_lt ((hN q).trans_lt hn), h0, h1, h2, zero_mul,
      mul_zero, sub_zero, add_zero]

/-- Check the Laplace equation coefficientwise by cross-multiplying integer rows. -/
@[expose]
public def MiddleIntRow.momentMatches (N : ℕ) (a b : ℤ) (p m : MiddleIntRow) : Bool :=
  (List.range (N + 1)).all
    (fun i ↦ decide (p.den * (a * m.num i - b * (i + 1 : ℕ) * m.num (i + 1)) = b * m.den * p.num i))

/-- A matching integer row represents the unshifted Laplace moment at rate `a / b`. -/
public theorem MiddleIntRow.poly_of_momentMatches {N : ℕ} {a b : ℤ} {p m : MiddleIntRow}
    (ha : a ≠ 0) (hb : b ≠ 0) (hp : p.den ≠ 0) (hm : m.den ≠ 0) (hs : m.nums.size ≤ N + 1)
    (h : p.momentMatches N a b m = true) :
    m.poly N = middleMomentPoly (p.poly N) ((a : ℚ) / b) 0 := by
  have ha' : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hb' : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hp' : (p.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hm' : (m.den : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
  apply middle_moment_eq_of_coeff (div_ne_zero ha' hb')
  intro i
  by_cases hi : i ≤ N
  · have he :=
      of_decide_eq_true (List.all_eq_true.mp h i (List.mem_range.mpr (Nat.lt_succ_of_le hi)))
    have hr := congrArg (fun x : ℤ => (x : ℚ)) he
    simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast] at hr
    rw [m.poly_coeff hi, m.poly_coeff_all N hs, p.poly_coeff hi]
    field_simp (disch :=
      first
      | exact hb'
      | exact hp'
      | exact hm')
    linear_combination hr
  · have hN (r : MiddleIntRow) : (r.poly N).natDegree ≤ N :=
      Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (Nat.succ_pos N) _)
    have hn := Nat.lt_of_not_ge hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hN m).trans_lt hn),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hN m).trans_lt (Nat.lt_succ_of_lt hn)),
      Polynomial.coeff_eq_zero_of_natDegree_lt ((hN p).trans_lt hn), mul_zero, zero_mul, sub_zero]

/-- Evaluate the row at `a / b` by taking the constant coefficient after translation. -/
public theorem MiddleIntRow.eval_eq_shift_head (r : MiddleIntRow) (N : ℕ) (a b : ℤ) (hr : r.den ≠ 0)
    (hb : b ≠ 0) :
    (r.poly N).eval ((a : ℚ) / b) = ((r.shift N a b).num 0 : ℚ) / (r.shift N a b).den := by
  have h := congrArg (fun P : Polynomial ℚ => P.coeff 0) (r.poly_shift N a b hr hb)
  rw [MiddleIntRow.poly_coeff _ (Nat.zero_le N), Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add] at h
  exact h.symm

/-- Evaluate the derivative at the shift by reading the linear coefficient
of the translated integer row. -/
public theorem MiddleIntRow.eval_deriv_eq_shift (r : MiddleIntRow) {N : ℕ} (hN : 1 ≤ N) (a b : ℤ)
    (hr : r.den ≠ 0) (hb : b ≠ 0) :
    (r.poly N).derivative.eval ((a : ℚ) / b) =
      ((r.shift N a b).num 1 : ℚ) / (r.shift N a b).den := by
  let Q := Polynomial.X + Polynomial.C ((a : ℚ) / b)
  have hm := congrArg (fun P : Polynomial ℚ ↦ P.derivative.eval 0) (r.poly_shift N a b hr hb)
  change ((r.shift N a b).poly N).derivative.eval 0 = ((r.poly N).comp Q).derivative.eval 0 at hm
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative, zero_add, Nat.cast_zero,
    zero_add, mul_one, MiddleIntRow.poly_coeff _ hN, Polynomial.derivative_comp,
    Polynomial.eval_mul, Polynomial.eval_comp] at hm
  simp only [Q, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, zero_add,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
    Polynomial.eval_one, one_mul] at hm
  exact hm.symm

end PseudoPrime.PrimeTestBounds.MillerRabin
