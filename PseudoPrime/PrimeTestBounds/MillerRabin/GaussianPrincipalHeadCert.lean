/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.Analysis.BernsteinIntegral
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalZeroVariation
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GCDMonoid.Finset
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData

/-! # Rational certification of the high principal head integral -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The profile polynomial before casting the manuscript's rational coefficients to reals. -/
@[expose]
public noncomputable def highRatProfile (K : HighGaussianKernel) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    Polynomial.monomial (K.logPower j) (K.expandedCoeff j / ((K.logPower j).factorial : ℚ))

/-- The real physical profile is the cast of the rational profile. -/
public theorem high_rat_profile_map (K : HighGaussianKernel) :
    (highRatProfile K).map (Rat.castHom ℝ) = K.realProfile := by
  simp only [highRatProfile, HighGaussianKernel.realProfile, Polynomial.map_sum,
    Polynomial.map_monomial, Rat.coe_castHom, Rat.cast_div, Rat.cast_natCast]

/-- The rational polynomial inside the absolute derivative integral of H26. -/
@[expose]
public noncomputable def highHeadRatPoly (K : HighGaussianKernel) : Polynomial ℚ :=
  let a := K.pole
  let B := highRatProfile K
  (Polynomial.C 5 - Polynomial.X) *
        (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative + Polynomial.C (a ^ 2) * B) -
      2 * B.derivative +
    Polynomial.C (2 * a) * B

/-- Casting the rational derivative polynomial gives precisely the integrand in H26. -/
public theorem high_head_rat_poly_map (K : HighGaussianKernel) :
    let a := (K.pole : ℝ)
    let B := K.realProfile
    (highHeadRatPoly K).map (Rat.castHom ℝ) =
      (Polynomial.C 5 - Polynomial.X) *
            (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative +
              Polynomial.C (a ^ 2) * B) -
          2 * B.derivative +
        Polynomial.C (2 * a) * B := by
  simp only [highHeadRatPoly, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, ← Polynomial.derivative_map, high_rat_profile_map,
    Rat.coe_castHom, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Polynomial.map_ofNat]

/-- Every monomial in the rational profile has degree at most `2 * degree + 3`. -/
private theorem high_rat_profile_degree (K : HighGaussianKernel) :
    (highRatProfile K).natDegree ≤ 2 * K.degree + 3 := by
  unfold highRatProfile
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.add_le_add_right (Nat.sub_le _ _) 3)

/-- The absolute derivative integral uses a polynomial with the profile degree raised by one. -/
public theorem high_head_rat_poly_degree (K : HighGaussianKernel) :
    (highHeadRatPoly K).natDegree ≤ 2 * K.degree + 4 := by
  let B := highRatProfile K
  let a := K.pole
  let n := 2 * K.degree + 3
  have hB : B.natDegree ≤ n := high_rat_profile_degree K
  have hD : B.derivative.natDegree ≤ n :=
    (Polynomial.natDegree_derivative_le B).trans ((Nat.sub_le _ _).trans hB)
  have hD' : B.derivative.derivative.natDegree ≤ n :=
    (Polynomial.natDegree_derivative_le B.derivative).trans ((Nat.sub_le _ _).trans hD)
  have hL : (Polynomial.C (5 : ℚ) - Polynomial.X).natDegree ≤ 1 := by
    apply (Polynomial.natDegree_sub_le _ _).trans
    rw [Polynomial.natDegree_C, Polynomial.natDegree_X, max_eq_right zero_le_one]
  have hM :
    (B.derivative.derivative - Polynomial.C (2 * a) * B.derivative +
          Polynomial.C (a ^ 2) * B).natDegree ≤
      n :=
    Polynomial.natDegree_add_le_of_degree_le
      ((Polynomial.natDegree_sub_le _ _).trans
        (max_le hD' ((Polynomial.natDegree_C_mul_le _ _).trans hD)))
      ((Polynomial.natDegree_C_mul_le _ _).trans hB)
  unfold highHeadRatPoly
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · exact (Polynomial.natDegree_mul_le_of_le hL hM).trans_eq (Nat.add_comm _ _)
    · change (Polynomial.C (2 : ℚ) * B.derivative).natDegree ≤ n + 1
      exact (Polynomial.natDegree_C_mul_le _ _).trans (hD.trans (Nat.le_succ n))
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (hB.trans (Nat.le_succ n))

/-- The reciprocal of the positive Taylor subtotal bounds the decreasing exponential. -/
@[expose]
public def headExpUpper (q : ℚ) (m : ℕ) : ℚ :=
  (∑ k ∈ Finset.range (m + 1), q ^ k / (k.factorial : ℚ))⁻¹

/-- For a nonnegative rational argument the Taylor subtotal is positive and
its reciprocal is an upper bound for `exp(-q)`. -/
public theorem head_exp_upper_sound {q : ℚ} (hq : 0 ≤ q) (m : ℕ) :
    Real.exp (-(q : ℝ)) ≤ (headExpUpper q m : ℝ) := by
  have hr : 0 ≤ (q : ℝ) := Rat.cast_nonneg.mpr hq
  have h0 : (1 : ℝ) ≤ ∑ k ∈ Finset.range (m + 1), (q : ℝ) ^ k / (k.factorial : ℝ) := by
    have h :=
      Finset.single_le_sum (f := fun k : ℕ ↦ (q : ℝ) ^ k / (k.factorial : ℝ))
        (fun k _ ↦ div_nonneg (pow_nonneg hr k) (Nat.cast_nonneg _))
        (Finset.mem_range.mpr (Nat.zero_lt_succ m))
    simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using h
  have hs := Real.sum_le_exp_of_nonneg hr (m + 1)
  simp only [headExpUpper, Rat.cast_inv, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Real.exp_neg]
  exact inv_le_inv₀ (Real.exp_pos _) (zero_lt_one.trans_le h0) |>.mpr hs

/-- The 32 equal Bernstein cells used for the head integral. -/
@[expose]
public def highHeadGrid (j : ℕ) : ℚ :=
  (5 : ℚ) * j / 32

/-- The rational Bernstein cell sum for the absolute derivative integral.
The Taylor parameter controls the exponential bounds at the cell endpoints. -/
@[expose]
public noncomputable def highHeadIntegralCharge (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  let n := 2 * K.degree + 4
  let P := highHeadRatPoly K
  ∑ j ∈ Finset.range 32,
    headExpUpper (K.pole * highHeadGrid j) m *
      ((highHeadGrid (j + 1) - highHeadGrid j) *
        ((∑ k : Fin (n + 1),
            |Analysis.bernsteinRatCoeff
                (P.comp
                  (Polynomial.C (highHeadGrid (j + 1) - highHeadGrid j) * Polynomial.X +
                    Polynomial.C (highHeadGrid j)))
                n k|) /
          ((n : ℚ) + 1)))

/-- A materialized row and the function used beyond its stored range. -/
private structure HeadCoeffCache (α : Type) where
  row : Array α
  fallback : ℕ → α

/-- Materialize a row before passing it to the arithmetic loops. -/
private def headCoeffCache {α : Type} (n : ℕ) (f : ℕ → α) : HeadCoeffCache α :=
  ⟨Array.ofFn (fun i : Fin n ↦ f i), f⟩

/-- Read a coefficient without reconstructing its row. -/
private def headCached {α : Type} (c : HeadCoeffCache α) (k : ℕ) : α :=
  match c.row[k]? with
  | some q => q
  | none => c.fallback k

/-- Reading a cached coefficient agrees with the original function. -/
private theorem head_coeff_cache_eq {α : Type} (n : ℕ) (f : ℕ → α) :
    headCached (headCoeffCache n f) = f := by
  funext k
  change
    (match (Array.ofFn fun i : Fin n ↦ f i)[k]? with
      | some q => q
      | none => f k) =
      f k
  rw [Array.getElem?_ofFn]
  by_cases h : k < n
  · rw [dite_eq_left h]
  · rw [dite_eq_right h]

/-- Compute the compact coefficient with an integer polynomial sum and one rational factor. -/
private def headCompactCoeff (K : HighGaussianKernel) (i : ℕ) : ℚ :=
  let v := coefficientTicks K
  if i ≤ K.degree then
    (-(2 * K.pole)) ^ (K.degree - i) / (v.sum : ℚ) *
      ((∑ j ∈ Finset.range (K.degree + 1),
            if K.degree - j ≤ i then (v[j]?.getD 0) * (Nat.fast_choose j (i - (K.degree - j)) : ℤ)
            else 0 :
          ℤ) :
        ℚ)
  else 0

/-- The binomial summands in a fixed coefficient all have the same pole power. -/
private theorem head_compact_power (d j i : ℕ) (hj : j ≤ d) (hi : d - j ≤ i) :
    j - (i - (d - j)) = d - i := by
  calc
    j - (i - (d - j)) = d - (d - j) - (i - (d - j)) :=
      congrArg (· - (i - (d - j))) (Nat.sub_sub_self hj).symm
    _ = d - i := by rw [Nat.sub_sub, Nat.add_sub_of_le hi]

/-- The integer computation gives exactly the compact polynomial coefficient. -/
private theorem head_compact_coeff_eq (K : HighGaussianKernel) (i : ℕ) :
    headCompactCoeff K i = compactCoeff K i := by
  by_cases hi : i ≤ K.degree
  · simp only [headCompactCoeff, ite_eq_left hi, Int.cast_sum, Finset.mul_sum, compactCoeff]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : K.degree - j ≤ i
    · simp only [ite_eq_left h, Int.cast_mul, Int.cast_natCast, ← Nat.choose_eq_fast_choose,
        head_compact_power K.degree j i (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) h]
      ring
    · simp only [ite_eq_right h, Int.cast_zero, mul_zero]
  · rw [headCompactCoeff, ite_eq_right hi, ← compact_coeff_eq]
    exact
      (Polynomial.coeff_eq_zero_of_natDegree_lt
          ((high_gaussian_polynomial_degree K).trans_lt (Nat.lt_of_not_ge hi))).symm

/-- The profile numerator uses the convolution of the compact power coefficients. -/
private def profileNumerator (K : HighGaussianKernel) (compact : ℕ → ℚ) (i : ℕ) : ℚ :=
  K.normalization * ∑ j ∈ Finset.range (i + 1), compact j * compact (i - j)

/-- The convolution computes the normalized squared coefficient in the profile. -/
private theorem profile_numerator_eq (K : HighGaussianKernel) (i : ℕ) :
    K.expandedCoeff i = profileNumerator K (compactCoeff K) i := by
  simp only [HighGaussianKernel.expandedCoeff, profileNumerator, pow_two, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, compact_coeff_eq]

/-- Each exponent in the reversed profile selects at most one numerator coefficient. -/
private theorem head_profile_index (N j k : ℕ) (hj : j ≤ N) :
    N - j + 3 = k ↔ 3 ≤ k ∧ k ≤ N + 3 ∧ j = N - (k - 3) := by
  constructor
  · rintro rfl
    exact
      ⟨Nat.le_add_left _ _, Nat.add_le_add_right (Nat.sub_le ..) _, by
        rw [Nat.add_sub_cancel_right, Nat.sub_sub_self hj]⟩
  · rintro ⟨hk, hN, rfl⟩
    rw [Nat.sub_sub_self (Nat.sub_le_sub_right hN 3 |>.trans_eq (Nat.add_sub_cancel_right N 3)),
      Nat.sub_add_cancel hk]

/-- Select the numerator term directly from the exponent, with zero outside the support. -/
private def highProfileFrom (K : HighGaussianKernel) (compact : HeadCoeffCache ℚ) (k : ℕ) : ℚ :=
  let N := 2 * K.degree
  if 3 ≤ k ∧ k ≤ N + 3 then
    profileNumerator K (headCached compact) (N - (k - 3)) / (k.factorial : ℚ)
  else 0

/-- Compute one profile coefficient from the compact power coefficients. -/
private def highProfileCoeff (K : HighGaussianKernel) : ℕ → ℚ :=
  highProfileFrom K (headCoeffCache (2 * K.degree + 1) (headCompactCoeff K))

/-- The coefficient formula for the rational profile. -/
private theorem high_profile_coeff_eq (K : HighGaussianKernel) (k : ℕ) :
    (highRatProfile K).coeff k = highProfileCoeff K k := by
  let N := 2 * K.degree
  simp only [highRatProfile, highProfileCoeff, highProfileFrom, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, Finsupp.single_apply, profile_numerator_eq, head_coeff_cache_eq,
    funext (head_compact_coeff_eq K)]
  change
    (∑ j ∈ Finset.range (N + 1),
        if N - j + 3 = k then profileNumerator K (compactCoeff K) j / ((N - j + 3).factorial : ℚ)
        else 0) =
      _
  by_cases hk : 3 ≤ k ∧ k ≤ N + 3
  · let j := N - (k - 3)
    have hj : j ∈ Finset.range (N + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le ..))
    have he := (head_profile_index N j k (Nat.sub_le ..)).2 ⟨hk.1, hk.2, rfl⟩
    rw [ite_eq_left hk, Finset.sum_eq_single_of_mem j hj]
    · rw [ite_eq_left he, he]
    · intro d hd hne
      exact
        ite_eq_right
          (fun h ↦
            hne ((head_profile_index N d k (Nat.le_of_lt_succ (Finset.mem_range.mp hd))).1 h).2.2)
  · rw [ite_eq_right hk]
    apply Finset.sum_eq_zero
    intro j hj
    exact
      ite_eq_right
        (fun h ↦
          hk
            ⟨((head_profile_index N j k (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).1 h).1,
              ((head_profile_index N j k (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).1 h).2.1⟩)

/-- The coefficients of the second derivative after removing the exponential factor. -/
private def highHeadInnerCoeff (a : ℚ) (profile : ℕ → ℚ) (k : ℕ) : ℚ :=
  profile (k + 1 + 1) * (k + 1 + 1 : ℕ) * (k + 1 : ℕ) - 2 * a * (profile (k + 1) * (k + 1 : ℕ)) +
    a ^ 2 * profile k

/-- The derivative polynomial in H26 is evaluated directly in the power basis. -/
private def highHeadCoeff (a : ℚ) (profile : ℕ → ℚ) (k : ℕ) : ℚ :=
  5 * highHeadInnerCoeff a profile k -
      (match k with
      | 0 => 0
      | d + 1 => highHeadInnerCoeff a profile d) -
      2 * (profile (k + 1) * (k + 1 : ℕ)) +
    2 * a * profile k

/-- The direct coefficient formula agrees with the H26 polynomial. -/
private theorem high_head_coeff_eq (K : HighGaussianKernel) (k : ℕ) :
    (highHeadRatPoly K).coeff k = highHeadCoeff K.pole (highProfileCoeff K) k := by
  cases k <;>
    simp only [highHeadRatPoly, highHeadCoeff, sub_mul, Polynomial.coeff_add, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_X_mul_zero, Polynomial.coeff_X_mul,
      Polynomial.coeff_derivative, highHeadInnerCoeff, high_profile_coeff_eq, Nat.cast_add,
      Nat.cast_one, ← Polynomial.C_ofNat]

/-- Compute the head charge from the derivative coefficients,
without constructing the affine polynomial on each cell. -/
private theorem high_head_integral_charge_sum (K : HighGaussianKernel) (m : ℕ) :
    let n := 2 * K.degree + 4
    highHeadIntegralCharge K m =
      ∑ j ∈ Finset.range 32,
        let l := highHeadGrid j
        let w := highHeadGrid (j + 1) - l
        headExpUpper (K.pole * l) m *
          (w *
            ((∑ k : Fin (n + 1),
                |∑ i ∈ Finset.range (n + 1),
                    (w ^ i *
                        ∑ d ∈ Finset.range (n + 1),
                          highHeadCoeff K.pole (highProfileCoeff K) d *
                            ((Nat.fast_choose d i : ℚ) * l ^ (d - i))) *
                      ((Nat.fast_choose k i : ℚ) / (Nat.fast_choose n i : ℚ))|) /
              ((n : ℚ) + 1))) := by
  simp only [highHeadIntegralCharge, Analysis.bernsteinRatCoeff,
    Analysis.rational_affine_coeff _ _ (high_head_rat_poly_degree K), high_head_coeff_eq,
    ← Nat.choose_eq_fast_choose]

/-- Lift the coefficients of a rational row to integers with one common denominator. -/
private def scaledHeadCoeff (D : ℕ) (q : ℚ) : ℤ :=
  q.num * (D / q.den : ℕ)

/-- Common-denominator scaling preserves each coefficient. -/
private theorem scaled_head_coeff_eq (D : ℕ) (q : ℚ) (hD : D ≠ 0) (hq : q.den ∣ D) :
    (scaledHeadCoeff D q : ℚ) / D = q := by
  have h := Nat.div_mul_cancel hq
  have hQ := congrArg (fun x : ℕ ↦ (x : ℚ)) h
  simp only [Nat.cast_mul] at hQ
  have hd : (D : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hq' : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  rw [scaledHeadCoeff, Int.cast_mul, Int.cast_natCast]
  apply Eq.trans _ q.num_div_den
  rw [div_eq_div_iff hd hq', mul_assoc, hQ]

/-- An integer dot product recovers the rational sum after one division. -/
private theorem scaled_head_dot (n D : ℕ) (hD : D ≠ 0) (c : Fin n → ℚ) (hc : ∀ i, (c i).den ∣ D)
    (w : Fin n → ℕ) :
    ((∑ i, scaledHeadCoeff D (c i) * (w i : ℤ) : ℤ) : ℚ) / D = ∑ i, c i * (w i : ℚ) := by
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_div_right_comm, scaled_head_coeff_eq D (c i) hD (hc i)]

/-- Sum the absolute Bernstein coefficients using integer numerators. -/
private def headBernsteinAbs (n : ℕ) (c : Fin (n + 1) → ℚ) (choose : ℕ → ℕ → ℕ) : ℚ :=
  let D := Finset.univ.lcm (fun i ↦ (c i).den)
  let row := Array.ofFn fun i : Fin (n + 1) ↦ scaledHeadCoeff D (c i)
  ((∑ k : Fin (n + 1), |∑ i : Fin (n + 1), row[i.val]?.getD 0 * (choose k i : ℤ)| : ℤ) : ℚ) / D

/-- A single division restores the sum of the absolute rational coefficients. -/
private theorem head_bernstein_abs_eq (n : ℕ) (c : Fin (n + 1) → ℚ) (choose : ℕ → ℕ → ℕ) :
    headBernsteinAbs n c choose =
      ∑ k : Fin (n + 1), |∑ i : Fin (n + 1), c i * (choose k i : ℚ)| := by
  let D := Finset.univ.lcm (fun i ↦ (c i).den)
  have hD : D ≠ 0 := fun h ↦
    let ⟨i, _, hi⟩ := Finset.lcm_eq_zero_iff.mp h
    (c i).den_nz hi
  have hc (i : Fin (n + 1)) : (c i).den ∣ D := Finset.dvd_lcm (Finset.mem_univ i)
  simp only [headBernsteinAbs, Array.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some,
    Int.cast_sum, Int.cast_abs, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℚ) D), ← abs_div]
  congr 1
  simpa only [Int.cast_sum] using scaled_head_dot (n + 1) D hD c hc (fun i ↦ choose k i)

/-- Pull a common power out of a shifted coefficient when the shift is nonzero. -/
private theorem head_affine_factor (n : ℕ) (c : Fin (n + 1) → ℚ) (l : ℚ) (hl : l ≠ 0)
    (i : Fin (n + 1)) :
    (∑ d : Fin (n + 1), (c d * l ^ d.val) * (Nat.fast_choose d i : ℚ)) / l ^ i.val =
      ∑ d : Fin (n + 1), c d * ((Nat.fast_choose d i : ℚ) * l ^ (d.val - i.val)) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : i.val ≤ d.val
  · apply (div_eq_iff (pow_ne_zero _ hl)).2
    have hp : l ^ (d.val - i.val) * l ^ i.val = l ^ d.val := by rw [← pow_add, Nat.sub_add_cancel h]
    rw [← hp]
    ring
  · simp only [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge h),
      Nat.cast_zero, mul_zero, zero_mul, zero_div]

/-- With zero shift only the diagonal term of the affine coefficient can survive. -/
private theorem head_affine_zero (n : ℕ) (coeffs : Fin (n + 1) → ℚ) (i : Fin (n + 1)) :
    (∑ d : Fin (n + 1), coeffs d * ((Nat.fast_choose d i : ℚ) * 0 ^ (d.val - i.val))) =
      coeffs i := by
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [Nat.sub_self, pow_zero, ← Nat.choose_eq_fast_choose, Nat.choose_self, Nat.cast_one,
      mul_one]
  · intro d _ hne
    rcases lt_or_gt_of_ne (fun h ↦ hne (Fin.ext h)) with h | h
    · simp only [← Nat.choose_eq_fast_choose, Nat.choose_eq_zero_of_lt h, Nat.cast_zero, zero_mul,
        mul_zero]
    · simp only [zero_pow (Nat.sub_ne_zero_of_lt h), mul_zero]

/-- Compute the affine coefficients with integer dot products when the shift is nonzero. -/
private def headAffineRow (n : ℕ) (coeffs : Fin (n + 1) → ℚ) (l w : ℚ) (choose : ℕ → ℕ → ℕ) :
    Array ℚ :=
  if l = 0 then Array.ofFn fun i : Fin (n + 1) ↦ w ^ i.val * coeffs i
  else
    let c := fun d : Fin (n + 1) ↦ coeffs d * l ^ d.val
    let D := Finset.univ.lcm (fun d ↦ (c d).den)
    let row := Array.ofFn fun d : Fin (n + 1) ↦ scaledHeadCoeff D (c d)
    Array.ofFn fun i : Fin (n + 1) ↦
      w ^ i.val *
        (((∑ d : Fin (n + 1), row[d.val]?.getD 0 * (choose d i : ℤ) : ℤ) : ℚ) / D / l ^ i.val)

/-- The integer affine calculation gives the original shifted coefficients. -/
private theorem head_affine_row_eq (n : ℕ) (coeffs : Fin (n + 1) → ℚ) (l w : ℚ) (i : Fin (n + 1)) :
    (headAffineRow n coeffs l w Nat.fast_choose)[i.val]?.getD 0 =
      w ^ i.val *
        ∑ d : Fin (n + 1), coeffs d * ((Nat.fast_choose d i : ℚ) * l ^ (d.val - i.val)) := by
  by_cases hl : l = 0
  · subst l
    simp only [headAffineRow, ite_true, Array.getElem?_ofFn, Fin.isLt, dite_true, Option.getD_some,
      head_affine_zero]
  · let c := fun d : Fin (n + 1) ↦ coeffs d * l ^ d.val
    let D := Finset.univ.lcm (fun d ↦ (c d).den)
    have hD : D ≠ 0 := fun h ↦
      let ⟨d, _, hd⟩ := Finset.lcm_eq_zero_iff.mp h
      (c d).den_nz hd
    have hc (d : Fin (n + 1)) : (c d).den ∣ D := Finset.dvd_lcm (Finset.mem_univ d)
    simp only [headAffineRow, ite_eq_right hl, Array.getElem?_ofFn, Fin.isLt, dite_true,
      Option.getD_some]
    rw [scaled_head_dot (n + 1) D hD c hc, head_affine_factor n coeffs l hl i]

/-- Evaluate a Bernstein cell reusing its shifted power coefficients. -/
private def headCellMass (n : ℕ) (coeffs : Fin (n + 1) → ℚ) (l w : ℚ) (choose : ℕ → ℕ → ℕ) : ℚ :=
  let row := headAffineRow n coeffs l w choose
  w * (headBernsteinAbs n (fun i ↦ row[i.val]?.getD 0 / (choose n i : ℚ)) choose / ((n : ℚ) + 1))

/-- Cache the derivative coefficients once, then evaluate the 32 weighted cells. -/
private def headIntegralTerms (K : HighGaussianKernel) (m : ℕ) : Array ℚ :=
  let n := 2 * K.degree + 4
  let choose := headCoeffCache (n + 1) (fun k ↦ headCoeffCache (n + 1) (Nat.fast_choose k))
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let profile := headCoeffCache (n + 3) (highProfileFrom K compact)
  let coeffs := headCoeffCache (n + 1) (highHeadCoeff K.pole (headCached profile))
  Array.ofFn fun j : Fin 32 ↦
    let l := highHeadGrid j
    headExpUpper (K.pole * l) m *
      headCellMass n (fun i ↦ headCached coeffs i) l (highHeadGrid (j + 1) - l)
        (fun k i ↦ headCached (headCached choose k) i)

/-- Sum the cached cell charges after each charge has been computed. -/
private def headIntegralFast (K : HighGaussianKernel) (m : ℕ) : ℚ :=
  let terms := headIntegralTerms K m
  ∑ j : Fin 32, terms[j.val]?.getD 0

/-- The cached affine row gives the same power sum within each cell. -/
private theorem head_cell_mass_eq (n : ℕ) (coeffs : Fin (n + 1) → ℚ) (l w : ℚ) :
    headCellMass n coeffs l w Nat.fast_choose =
      w *
        ((∑ k : Fin (n + 1),
            |∑ i : Fin (n + 1),
                (w ^ i.val *
                    ∑ d : Fin (n + 1),
                      coeffs d * ((Nat.fast_choose d i : ℚ) * l ^ (d.val - i.val))) *
                  ((Nat.fast_choose k i : ℚ) / (Nat.fast_choose n i : ℚ))|) /
          ((n : ℚ) + 1)) := by
  simp only [headCellMass, head_bernstein_abs_eq, head_affine_row_eq, div_mul_eq_mul_div,
    mul_div_assoc, mul_comm]

/-- Conversion to the finite-sum formula certifies the cached implementation. -/
private theorem head_integral_fast_eq (K : HighGaussianKernel) (m : ℕ) :
    headIntegralFast K m = highHeadIntegralCharge K m := by
  rw [high_head_integral_charge_sum]
  simp only [headIntegralFast, headIntegralTerms, Array.getElem?_ofFn, Fin.isLt, dite_true,
    Option.getD_some, head_coeff_cache_eq, head_cell_mass_eq, highProfileCoeff,
    ← Fin.sum_univ_eq_sum_range]

/-- The H26 head cap is bounded by the rational Bernstein sum and one rational endpoint charge. -/
public theorem high_head_cap_rat (K : HighGaussianKernel) (m : ℕ) :
    highPrincipalHeadCap K ≤
      ((headExpUpper (K.pole * 5) m * |(highRatProfile K).eval 5| + highHeadIntegralCharge K m :
          ℚ) :
        ℝ) := by
  have ha : 0 < (K.pole : ℝ) := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  have haQ := Rat.cast_pos.mp ha
  have h₁ := head_exp_upper_sound (mul_nonneg haQ.le (by norm_num only : (0 : ℚ) ≤ 5)) m
  have hp (j : ℕ) : highHeadGrid j < highHeadGrid (j + 1) := by
    unfold highHeadGrid
    exact
      div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left (Nat.cast_lt.mpr (Nat.lt_succ_self j)) (by norm_num only))
        (by norm_num only)
  have he (j : ℕ) :
    Real.exp (-(K.pole : ℝ) * (highHeadGrid j : ℝ)) ≤
      (headExpUpper (K.pole * highHeadGrid j) m : ℝ) := by
    have hq : 0 ≤ highHeadGrid j := by
      unfold highHeadGrid
      exact div_nonneg (mul_nonneg (by norm_num only) (Nat.cast_nonneg _)) (by norm_num only)
    simpa only [Rat.cast_mul, neg_mul] using head_exp_upper_sound (mul_nonneg haQ.le hq) m
  have hi :=
    Analysis.weighted_abs_rat_bernstein (highHeadRatPoly K) 32 (2 * K.degree + 4)
      (high_head_rat_poly_degree K) ha.le highHeadGrid
      (fun j ↦ headExpUpper (K.pole * highHeadGrid j) m) (fun j _ ↦ hp j) (fun j _ ↦ he j)
  have hzero : highHeadGrid 0 = 0 := by
    norm_num only [highHeadGrid, Nat.cast_zero, mul_zero, zero_div]
  have hlast : highHeadGrid 32 = 5 := by norm_num only [highHeadGrid, Nat.cast_ofNat]
  rw [hzero, hlast, Rat.cast_zero, Rat.cast_ofNat] at hi
  have hD := high_head_rat_poly_map K
  have hB := high_rat_profile_map K
  have hcast : (((highRatProfile K).eval (5 : ℚ) : ℚ) : ℝ) = K.realProfile.eval 5 := by
    simpa only [hB, Rat.coe_castHom, Rat.cast_ofNat] using
      (Polynomial.eval_map_apply (p := highRatProfile K) (Rat.castHom ℝ) (5 : ℚ)).symm
  simp only [Rat.cast_mul, Rat.cast_ofNat] at h₁
  dsimp only [highPrincipalHeadCap] at ⊢
  dsimp only at hD
  rw [← hD, ← hcast]
  simp only [Polynomial.eval_map, Rat.cast_add, Rat.cast_mul, Rat.cast_abs]
  simpa only [neg_mul, highHeadIntegralCharge] using
    add_le_add (mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)) hi

/-- Evaluate the rational profile at the right endpoint directly from its coefficients. -/
private def headEndpointFast (K : HighGaussianKernel) : ℚ :=
  let compact := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  ∑ j ∈ Finset.range (2 * K.degree + 1),
    (profileNumerator K (headCached compact) j / ((K.logPower j).factorial : ℚ)) *
      (5 : ℚ) ^ K.logPower j

/-- The direct endpoint evaluation agrees with the profile polynomial. -/
private theorem head_endpoint_fast_eq (K : HighGaussianKernel) :
    headEndpointFast K = (highRatProfile K).eval 5 := by
  simp only [headEndpointFast, highRatProfile, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
    profile_numerator_eq, head_coeff_cache_eq, funext (head_compact_coeff_eq K)]

/-- Compute the H26 head cap with rational arithmetic and a truncated Taylor subtotal. -/
private def headCapFast (K : HighGaussianKernel) : ℚ :=
  headExpUpper (K.pole * 5) 36 * |headEndpointFast K| + headIntegralFast K 36

/-- The evaluator returns the rational upper bound from the Bernstein proof. -/
private theorem head_cap_fast_sound (K : HighGaussianKernel) :
    highPrincipalHeadCap K ≤ (headCapFast K : ℝ) := by
  simpa only [headCapFast, head_endpoint_fast_eq, head_integral_fast_eq] using
    high_head_cap_rat K 36

/-- Replacing the head integral by the rational certificate gives a cap on
the variation across a positive zero bracket. -/
public theorem high_principal_midpoint_rat (K : HighGaussianKernel) (m : ℕ) {l r t : ℝ} (hl : 0 < l)
    (ht : t ∈ Set.Icc l r) :
    let a := (K.pole : ℝ)
    let M₀ := highCompactMass K
    let M₁ := highCompactSlope K
    let C :=
      (headExpUpper (K.pole * 5) m * |(highRatProfile K).eval 5| + highHeadIntegralCharge K m : ℚ)
    ‖highPrincipalMultiplier K t‖ ≤
      ‖highPrincipalMultiplier K ((l + r) / 2)‖ +
        (3 * (K.normalization : ℝ) *
              (5 * M₀ ^ 2 / l ^ 4 + 4 * M₀ ^ 2 / l ^ 5 + 4 * a * M₀ * M₁ / l ^ 6) +
            4 * (C : ℝ) / l ^ 2 +
            4 * |highPrincipalEdge K| / (l ^ 2 + 1 / 4)) *
          ((r - l) / 2) := by
  intro a M₀ M₁ C
  have hc := high_head_cap_rat K m
  have h := high_principal_multiplier_midpoint K hl ht
  refine
    h.trans
      (add_le_add le_rfl
        (mul_le_mul_of_nonneg_right ?_
          (div_nonneg (sub_nonneg.mpr (ht.1.trans ht.2)) (by norm_num only))))
  unfold highPrincipalDerivCap
  exact
    add_le_add
      (add_le_add le_rfl
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num only))
          (sq_nonneg _)))
      le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
