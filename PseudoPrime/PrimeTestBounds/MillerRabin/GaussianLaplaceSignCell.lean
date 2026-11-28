/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
public import PseudoPrime.Analysis.BernsteinIntegral
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLaplaceMoment
import PseudoPrime.Analysis.ExponentialTaylorCertificates
import PseudoPrime.Analysis.GammaExpRationalBounds

/-! # Exact negative moments on sign-certified cells -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a nonnegative cell the weighted negative moment vanishes. -/
public theorem negative_moment_eq_zero (P : Polynomial ℝ) (s : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hP : ∀ t ∈ Set.Icc a b, 0 ≤ P.eval t) :
    (∫ t in a..b, Real.exp (-s * t) * max 0 (-P.eval t)) = 0 := by
  nth_rw 2 [← intervalIntegral.integral_zero (a := a) (b := b)]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  simp only [max_eq_left (neg_nonpos.mpr (hP t ht)), mul_zero]

/-- On a nonpositive cell the weighted negative moment is the difference
of two signed tails. It can be evaluated using the exact endpoint moments. -/
public theorem negative_moment_eq_tail_sub (P : Polynomial ℝ) {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hab : a ≤ b) (hP : ∀ t ∈ Set.Icc a b, P.eval t ≤ 0) :
    let f := fun t : ℝ ↦ P.eval t * Real.exp (-s * t)
    (∫ t in a..b, Real.exp (-s * t) * max 0 (-P.eval t)) =
      (∫ t in Set.Ioi b, f t) - (∫ t in Set.Ioi a, f t) := by
  intro f
  have hf : MeasureTheory.IntegrableOn f (Set.Ioi a) := by
    apply
      ((abs_laplace_integrable_and_le P hs).1.mono_set (Set.Ioi_subset_Ioi ha)).mono'
        (P.continuous.mul
            (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
    exact
      Filter.Eventually.of_forall fun t ↦ by
        change ‖P.eval t * Real.exp (-s * t)‖ ≤ Real.exp (-s * t) * |P.eval t|
        rw [mul_comm (P.eval t), Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [← neg_sub, intervalIntegral.integral_Ioi_sub_Ioi hf hab, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  simp only [max_eq_right (neg_nonneg.mpr (hP t ht)), f, mul_neg, mul_comm, neg_mul]

/-- The nonpositive cell charge reduces to two finite signed polynomial
moments with exponential factors evaluated at the endpoints. -/
public theorem negative_moment_eq_endpoints (P : Polynomial ℝ) {s a b : ℝ} (hs : 0 < s) (ha : 0 ≤ a)
    (hab : a ≤ b) (hP : ∀ t ∈ Set.Icc a b, P.eval t ≤ 0) :
    let M := fun z ↦
      let Q := P.comp (Polynomial.X + Polynomial.C z)
      Real.exp (-s * z) *
        ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℝ) / s ^ (k + 1))
    (∫ t in a..b, Real.exp (-s * t) * max 0 (-P.eval t)) = M b - M a := by
  intro M
  rw [negative_moment_eq_tail_sub P hs ha hab hP, polynomial_exp_tail P b hs,
    polynomial_exp_tail P a hs]

/-- The affine Bernstein representation at a physical point of a rational
cell uses a normalized point in the closed unit interval. -/
private theorem sign_cell_bernstein_eval (P : Polynomial ℚ) {n : ℕ} (hP : P.natDegree ≤ n) {a b : ℚ}
    (hab : a < b) {t : ℝ} (ht : t ∈ Set.Icc (a : ℝ) (b : ℝ)) :
    ∃ x : Set.Icc (0 : ℝ) 1,
      (P.map (Rat.castHom ℝ)).eval t =
        ∑ i : Fin (n + 1),
          (Analysis.bernsteinRatCoeff
                (P.comp (Polynomial.C (b - a) * Polynomial.X + Polynomial.C a)) n i :
              ℝ) *
            bernstein n i x := by
  let h := ((b : ℝ) - a)
  have hh : 0 < h := sub_pos.mpr (Rat.cast_lt.mpr hab)
  let x : Set.Icc (0 : ℝ) 1 :=
    ⟨(t - a) / h, div_nonneg (sub_nonneg.mpr ht.1) hh.le,
      (div_le_one hh).mpr (sub_le_sub_right ht.2 _)⟩
  have hx : (((b - a : ℚ) : ℝ) * x + (a : ℝ)) = t := by
    rw [Rat.cast_sub]
    change h * ((t - a) / h) + (a : ℝ) = t
    rw [mul_comm h, div_mul_cancel₀ _ hh.ne', sub_add_cancel]
  refine ⟨x, ?_⟩
  rw [Polynomial.eval_map, ← hx]
  exact Analysis.bernstein_rat_affine_eval P n hP a b x

/-- A rational Bernstein sign check implies the corresponding pointwise
sign on the entire closed cell. Both signs use the same affine representation. -/
public theorem bernstein_cell_nonneg (P : Polynomial ℚ) {n : ℕ} (hP : P.natDegree ≤ n) {a b : ℚ}
    (hab : a < b) :
    let Q := P.comp (Polynomial.C (b - a) * Polynomial.X + Polynomial.C a)
    let c := fun i : Fin (n + 1) ↦ Analysis.bernsteinRatCoeff Q n i
    (∀ i, 0 ≤ c i) → (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), 0 ≤ (P.map (Rat.castHom ℝ)).eval t) := by
  intro Q c hc t ht
  obtain ⟨x, hx⟩ := sign_cell_bernstein_eval P hP hab ht
  rw [hx]
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (Rat.cast_nonneg.mpr (hc i)) bernstein_nonneg

/-- Nonpositive affine Bernstein coefficients certify a nonpositive physical cell. -/
public theorem bernstein_cell_nonpos (P : Polynomial ℚ) {n : ℕ} (hP : P.natDegree ≤ n) {a b : ℚ}
    (hab : a < b)
    (hc :
      ∀ i : Fin (n + 1),
        Analysis.bernsteinRatCoeff (P.comp (Polynomial.C (b - a) * Polynomial.X + Polynomial.C a)) n
            i ≤
          0) :
    ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), (P.map (Rat.castHom ℝ)).eval t ≤ 0 := by
  intro t ht
  obtain ⟨x, hx⟩ := sign_cell_bernstein_eval P hP hab ht
  rw [hx]
  exact
    Finset.sum_nonpos fun i _ ↦
      mul_nonpos_of_nonpos_of_nonneg (Rat.cast_nonpos.mpr (hc i)) bernstein_nonneg

/-- The rational factor in a signed polynomial tail, after translating to
the endpoint and integrating each exponential monomial. -/
public noncomputable def signedTailFactor (P : Polynomial ℚ) (s z : ℚ) : ℚ :=
  let Q := P.comp (Polynomial.X + Polynomial.C z)
  ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * ((k.factorial : ℚ) / s ^ (k + 1))

/-- Any upper bound on the translated degree may be used in the finite
Laplace factor since all added coefficients are zero. -/
public theorem signed_tail_factor_sum (P : Polynomial ℚ) (s z : ℚ) (n : ℕ)
    (hn : (P.comp (Polynomial.X + Polynomial.C z)).natDegree ≤ n) :
    signedTailFactor P s z =
      ∑ k ∈ Finset.range (n + 1),
        (P.comp (Polynomial.X + Polynomial.C z)).coeff k * ((k.factorial : ℚ) / s ^ (k + 1)) := by
  unfold signedTailFactor
  refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ hn)) ?_
  intro k _ hk
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_not_ge (fun h ↦ hk (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))),
    zero_mul]

/-- Casting the rational factor gives the exact signed real Laplace tail
after multiplication by the endpoint exponential. -/
public theorem signed_tail_factor_eq (P : Polynomial ℚ) {s : ℚ} (hs : 0 < s) (z : ℚ) :
    (∫ t in Set.Ioi (z : ℝ), (P.map (Rat.castHom ℝ)).eval t * Real.exp (-(s : ℝ) * t)) =
      Real.exp (-(s : ℝ) * (z : ℝ)) * (signedTailFactor P s z : ℝ) := by
  let Q := P.comp (Polynomial.X + Polynomial.C z)
  have hQ :
    Q.map (Rat.castHom ℝ) = (P.map (Rat.castHom ℝ)).comp (Polynomial.X + Polynomial.C (z : ℝ)) := by
    rw [Polynomial.map_comp, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
      Rat.coe_castHom]
  rw [polynomial_exp_tail _ _ (Rat.cast_pos.mpr hs)]
  have hi : Function.Injective (Rat.castHom ℝ) := Rat.cast_injective
  simp only [← hQ, Polynomial.natDegree_map_eq_of_injective hi, Polynomial.coeff_map,
    Rat.coe_castHom, signedTailFactor, Q, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast]

/-- Interval multiplication by a signed endpoint factor is enclosed by
the minimum and maximum of the two endpoint products. -/
private theorem signed_product_bounds (f x l u : ℝ) (hl : l ≤ x) (hu : x ≤ u) :
    min (l * f) (u * f) ≤ x * f ∧ x * f ≤ max (l * f) (u * f) := by
  by_cases hf : 0 ≤ f
  · exact
      ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hl hf),
        (mul_le_mul_of_nonneg_right hu hf).trans (le_max_right _ _)⟩
  · have hf' := le_of_not_ge hf
    exact
      ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hu hf'),
        (mul_le_mul_of_nonpos_right hl hf').trans (le_max_left _ _)⟩

/-- A nonpositive rational cell can be charged using only its two
signed factors and rational enclosures for the endpoint exponentials. -/
public theorem negative_cell_le_endpoint_ranges (P : Polynomial ℚ) {s a b : ℚ} (hs : 0 < s)
    (ha : 0 ≤ a) (hab : a ≤ b)
    (hP : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), (P.map (Rat.castHom ℝ)).eval t ≤ 0) (la ua lb ub : ℚ)
    (hleft : (la : ℝ) ≤ Real.exp (-(s : ℝ) * (a : ℝ)) ∧ Real.exp (-(s : ℝ) * (a : ℝ)) ≤ (ua : ℝ))
    (hright : (lb : ℝ) ≤ Real.exp (-(s : ℝ) * (b : ℝ)) ∧ Real.exp (-(s : ℝ) * (b : ℝ)) ≤ (ub : ℝ)) :
    let f := signedTailFactor P s a
    let g := signedTailFactor P s b
    (∫ t in (a : ℝ)..(b : ℝ), Real.exp (-(s : ℝ) * t) * max 0 (-(P.map (Rat.castHom ℝ)).eval t)) ≤
      ((max (lb * g) (ub * g) - min (la * f) (ua * f) : ℚ) : ℝ) := by
  intro f g
  rw [negative_moment_eq_tail_sub _ (Rat.cast_pos.mpr hs) (Rat.cast_nonneg.mpr ha)
      (Rat.cast_le.mpr hab) hP,
    signed_tail_factor_eq P hs a, signed_tail_factor_eq P hs b]
  simp only [Rat.cast_sub, Rat.cast_max, Rat.cast_min, Rat.cast_mul]
  exact
    sub_le_sub (signed_product_bounds g _ _ _ hright.1 hright.2).2
      (signed_product_bounds f _ _ _ hleft.1 hleft.2).1

/-- A rational lower bound for the negative exponential at the high-kernel
endpoints. Divide the height by sixteen before taking the Taylor bound. -/
public def negativeEndpointExpLower (x : ℚ) : ℚ :=
  Analysis.gammaExpTaylorLower (x / 16) 32 ^ 16

/-- The endpoint lower bound is valid on the entire height range used
by K186 and K196, including both terminal sign boundaries. -/
public theorem negative_endpoint_exp_lower_valid {x : ℚ} (hx₀ : 0 ≤ x) (hx : x ≤ 264) :
    (negativeEndpointExpLower x : ℝ) ≤ Real.exp (-(x : ℝ)) := by
  have hsize : (x / 16 : ℚ) / ((32 + 1 : ℕ) : ℚ) ≤ 1 / 2 := by
    norm_num only [Nat.reduceAdd, Nat.cast_ofNat]
    linarith only [hx]
  have h :=
    Analysis.gamma_exp_taylor_lower_valid (div_nonneg hx₀ (by norm_num only : (0 : ℚ) ≤ 16)) hsize
  have h₀ : 0 ≤ Analysis.gammaExpTaylorLower (x / 16) 32 := by
    unfold Analysis.gammaExpTaylorLower
    exact
      inv_nonneg.mpr
        (add_nonneg
          (Finset.sum_nonneg fun i _ ↦
            div_nonneg (pow_nonneg (div_nonneg hx₀ (by norm_num only)) i) (Nat.cast_nonneg _))
          (mul_nonneg
            (div_nonneg (pow_nonneg (div_nonneg hx₀ (by norm_num only)) 32) (Nat.cast_nonneg _))
            (by norm_num only)))
  have hp := pow_le_pow_left₀ (Rat.cast_nonneg.mpr h₀) h 16
  rw [← Real.exp_natCast_mul] at hp
  have h16 : (16 : ℝ) ≠ 0 := by norm_num only
  simpa only [negativeEndpointExpLower, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat,
    neg_div, mul_neg, mul_div_cancel₀ _ h16] using hp

/-- At signed endpoints use a smaller Taylor argument so the upper bound
does not lose precision when subtracting two nearby signed moments. -/
public def negativeEndpointExpUpper (x : ℚ) : ℚ :=
  Analysis.gammaExpTaylorUpper (x / 64) ^ 64

/-- The rescaled reciprocal Taylor sum bounds the negative exponential. -/
public theorem negative_endpoint_exp_upper_valid {x : ℚ} (hx : 0 ≤ x) :
    Real.exp (-(x : ℝ)) ≤ (negativeEndpointExpUpper x : ℝ) := by
  have h := Analysis.gamma_exp_taylor_upper_valid (div_nonneg hx (by norm_num only : (0 : ℚ) ≤ 64))
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 64
  rw [← Real.exp_natCast_mul] at hp
  have hn : (64 : ℝ) ≠ 0 := by norm_num only
  simpa only [negativeEndpointExpUpper, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat,
    neg_div, mul_neg, mul_div_cancel₀ _ hn] using hp

end PseudoPrime.PrimeTestBounds.MillerRabin
