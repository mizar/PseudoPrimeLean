/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.BernsteinMoments
public import PseudoPrime.Analysis.GammaExpRationalBounds
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Clipping negative Bernstein coefficients on a compensation cell -/

public section

namespace PseudoPrime.Analysis

/-- The polynomial with Bernstein coefficients given by the negative part
of the source coefficients. Its variable is normalized to the unit interval. -/
@[expose]
noncomputable def bernsteinCompensation (P : Polynomial ℚ) (n : ℕ) : Polynomial ℝ :=
  ∑ i : Fin (n + 1),
    Polynomial.C (max 0 (-(bernsteinRatCoeff P n i.val : ℝ))) * bernsteinPolynomial ℝ n i.val

private theorem compensation_eval (P : Polynomial ℚ) (n : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (bernsteinCompensation P n).eval (t : ℝ) =
      ∑ i : Fin (n + 1), max 0 (-(bernsteinRatCoeff P n i.val : ℝ)) * bernstein n i.val t := by
  simp only [bernsteinCompensation, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  rfl

/-- Coefficient clipping gives a nonnegative compensation on the unit
cell, and adding it makes the source polynomial nonnegative there. -/
theorem bernstein_compensation_nonneg (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ (bernsteinCompensation P n).eval (t : ℝ) ∧
      0 ≤ P.eval₂ (Rat.castHom ℝ) (t : ℝ) + (bernsteinCompensation P n).eval (t : ℝ) := by
  rw [compensation_eval, bernstein_rat_coeff_eval P n hP]
  refine ⟨Finset.sum_nonneg (fun _ _ ↦ mul_nonneg (le_max_left _ _) bernstein_nonneg), ?_⟩
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_nonneg
  intro i _
  rw [← add_mul]
  exact
    mul_nonneg (by linarith only [le_max_right (0 : ℝ) (-(bernsteinRatCoeff P n i.val : ℝ))])
      bernstein_nonneg

private theorem bernstein_eval_zero_select (n : ℕ) (c : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), c i * (bernsteinPolynomial ℝ n i.val).eval 0) = c 0 := by
  rw [Finset.sum_eq_single (0 : Fin (n + 1))]
  · simp only [bernsteinPolynomial.eval_at_0, Fin.val_zero, ite_true, mul_one]
  · intro i _ hi
    have h : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
    simp only [bernsteinPolynomial.eval_at_0, ite_eq_right h, mul_zero]
  · exact fun h ↦ (h (Finset.mem_univ _)).elim

private theorem bernstein_eval_one_select (n : ℕ) (c : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), c i * (bernsteinPolynomial ℝ n i.val).eval 1) = c (Fin.last n) := by
  rw [Finset.sum_eq_single (Fin.last n)]
  · simp only [bernsteinPolynomial.eval_at_1, Fin.val_last, ite_true, mul_one]
  · intro i _ hi
    have h : i.val ≠ n := fun h ↦ hi (Fin.ext h)
    simp only [bernsteinPolynomial.eval_at_1, ite_eq_right h, mul_zero]
  · exact fun h ↦ (h (Finset.mem_univ _)).elim

/-- At the left endpoint, clipping agrees with the negative part of the
source value. This identifies the common value at a partition seam. -/
theorem bernstein_compensation_at_zero (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) :
    (bernsteinCompensation P n).eval 0 = max 0 (-(P.eval₂ (Rat.castHom ℝ) 0)) := by
  have h := bernstein_rat_coeff_eval P n hP ⟨0, le_rfl, zero_le_one⟩
  change
    P.eval₂ (Rat.castHom ℝ) 0 =
      ∑ i : Fin (n + 1),
        (bernsteinRatCoeff P n i.val : ℝ) * (bernsteinPolynomial ℝ n i.val).eval 0 at h
  rw [bernstein_eval_zero_select] at h
  simp only [bernsteinCompensation, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [bernstein_eval_zero_select, h]

/-- At the right endpoint, clipping agrees with the negative part of the
source value, independently of the degree used on an adjacent cell. -/
theorem bernstein_compensation_at_one (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) :
    (bernsteinCompensation P n).eval 1 = max 0 (-(P.eval₂ (Rat.castHom ℝ) 1)) := by
  have h := bernstein_rat_coeff_eval P n hP ⟨1, zero_le_one, le_rfl⟩
  change
    P.eval₂ (Rat.castHom ℝ) 1 =
      ∑ i : Fin (n + 1),
        (bernsteinRatCoeff P n i.val : ℝ) * (bernsteinPolynomial ℝ n i.val).eval 1 at h
  rw [bernstein_eval_one_select] at h
  simp only [bernsteinCompensation, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C]
  rw [bernstein_eval_one_select, h]

/-- Affine substitution in a rational polynomial preserves the degree upper bound. -/
theorem bernstein_affine_degree (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) (l r : ℚ) :
    (P.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l)).natDegree ≤ n := by
  have h : (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l).natDegree ≤ 1 := by
    rw [Polynomial.natDegree_add_C]
    exact (Polynomial.natDegree_C_mul_le _ _).trans_eq Polynomial.natDegree_X
  exact
    (Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul_left _ h)).trans ((Nat.mul_one _).symm ▸ hP)

/-- On a rational affine cell, the compensation is nonnegative and offsets
the source polynomial evaluated at the corresponding physical coordinate. -/
theorem bernstein_affine_compensation_nonneg (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    (l r : ℚ) (t : Set.Icc (0 : ℝ) 1) :
    let C := bernsteinCompensation (P.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l)) n
    0 ≤ C.eval (t : ℝ) ∧
      0 ≤ P.eval₂ (Rat.castHom ℝ) (((r - l : ℚ) : ℝ) * t + (l : ℝ)) + C.eval (t : ℝ) := by
  have h := bernstein_compensation_nonneg _ n (bernstein_affine_degree P n hP l r) t
  simpa only [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Rat.coe_castHom] using h

/-- On adjacent rational cells, the normalized compensation polynomials
agree at their shared endpoint, even if the Bernstein degrees differ. -/
theorem bernstein_compensation_seam (P : Polynomial ℚ) (n m : ℕ) (hn : P.natDegree ≤ n)
    (hm : P.natDegree ≤ m) (l r s : ℚ) :
    (bernsteinCompensation (P.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l)) n).eval
        1 =
      (bernsteinCompensation (P.comp (Polynomial.C (s - r) * Polynomial.X + Polynomial.C r)) m).eval
        0 := by
  rw [bernstein_compensation_at_one _ _ (bernstein_affine_degree P n hn l r),
    bernstein_compensation_at_zero _ _ (bernstein_affine_degree P m hm r s)]
  simp only [Polynomial.eval₂_comp, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X, Rat.coe_castHom, mul_one, mul_zero, zero_add, Rat.cast_sub, sub_add_cancel]

/-- On a cell of positive width, integrate the compensation against a
monomial using exact Bernstein moments of the clipped rational coefficients. -/
theorem bernstein_compensation_moment (P : Polynomial ℚ) (n j : ℕ) {h : ℝ} (hh : 0 < h) :
    (∫ t in 0..h, t ^ j * (bernsteinCompensation P n).eval (t / h)) =
      ∑ i : Fin (n + 1),
        (↑(max 0 (-bernsteinRatCoeff P n i.val)) : ℝ) *
          (h ^ (j + 1) *
            ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) / ((n + j : ℕ) + 1))) := by
  apply bernstein_profile_moment hh
  intro t _
  simp only [bernsteinCompensation, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, bernsteinPolynomial, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_natCast, Rat.cast_max, Rat.cast_zero,
    Rat.cast_neg]

/-- A continuous majorant of the weight on a positive-width cell also
majorizes the weighted compensation integral. -/
theorem bernstein_compensation_integral_le (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) {h : ℝ}
    (hh : 0 < h) {w U : ℝ → ℝ} (hw : Continuous w) (hU : Continuous U)
    (hle : ∀ t ∈ Set.Icc 0 h, w t ≤ U t) :
    (∫ t in 0..h, w t * (bernsteinCompensation P n).eval (t / h)) ≤
      ∫ t in 0..h, U t * (bernsteinCompensation P n).eval (t / h) := by
  have hc := (bernsteinCompensation P n).continuous.comp (continuous_id.div_const h)
  refine
    intervalIntegral.integral_mono_on hh.le ((hw.mul hc).intervalIntegrable _ _)
      ((hU.mul hc).intervalIntegrable _ _) (fun t ht ↦ ?_)
  let u : Set.Icc (0 : ℝ) 1 := ⟨t / h, div_nonneg ht.1 hh.le, (div_le_one hh).mpr ht.2⟩
  exact mul_le_mul_of_nonneg_right (hle t ht) (bernstein_compensation_nonneg P n hP u).1

/-- A polynomial upper bound on the weight reduces the compensation charge
to a finite sum of monomial moments. -/
theorem bernstein_compensation_taylor_le (P : Polynomial ℚ) (n N : ℕ) (hP : P.natDegree ≤ n) {h : ℝ}
    (hh : 0 < h) {w : ℝ → ℝ} (hw : Continuous w) (d : ℕ → ℝ)
    (hle : ∀ t ∈ Set.Icc 0 h, w t ≤ ∑ j ∈ Finset.range N, d j * t ^ j) :
    (∫ t in 0..h, w t * (bernsteinCompensation P n).eval (t / h)) ≤
      ∑ j ∈ Finset.range N,
        d j *
          (∑ i : Fin (n + 1),
            (↑(max 0 (-bernsteinRatCoeff P n i.val)) : ℝ) *
              (h ^ (j + 1) *
                ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) /
                  ((n + j : ℕ) + 1)))) := by
  let C := fun t : ℝ ↦ (bernsteinCompensation P n).eval (t / h)
  have hc : Continuous C := (bernsteinCompensation P n).continuous.comp (continuous_id.div_const h)
  have hmono :=
    bernstein_compensation_integral_le P n hP hh hw
      (continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_id.pow j))) hle
  refine hmono.trans_eq ?_
  change (∫ t in 0..h, (∑ j ∈ Finset.range N, d j * t ^ j) * C t) = _
  simp only [Finset.sum_mul, mul_assoc]
  have hi (j : ℕ) : IntervalIntegrable (fun t : ℝ ↦ d j * (t ^ j * C t)) MeasureTheory.volume 0 h :=
    (continuous_const.mul ((continuous_id.pow j).mul hc)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  exact congrArg (d j * ·) (bernstein_compensation_moment P n j hh)

/-- For nonnegative arguments of a decaying exponential, the even Taylor
truncations majorize the exponential by the sign of the Lagrange remainder. -/
theorem exp_decay_le_even_taylor {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (m : ℕ) :
    Real.exp (-s * t) ≤ ∑ j ∈ Finset.range (2 * m + 1), ((-s) ^ j / (j.factorial : ℝ)) * t ^ j := by
  rcases ht.eq_or_lt with rfl | ht
  · simp only [mul_zero, Real.exp_zero, Finset.sum_range_succ', pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, zero_pow (Nat.succ_ne_zero _), mul_zero,
      Finset.sum_const_zero, zero_add, le_refl]
  let f := fun x : ℝ ↦ Real.exp (-s * x)
  have hf : ContDiff ℝ ⊤ f := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hne : (0 : ℝ) ≠ t := ht.ne
  obtain ⟨x, _, hx⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (n := 2 * m) hne (hf.of_le le_top).contDiffOn
  have hr :
    iteratedDeriv (2 * m + 1) f x * (t - 0) ^ (2 * m + 1) / (((2 * m + 1 : ℕ).factorial : ℝ)) ≤
      0 := by
    rw [show iteratedDeriv (2 * m + 1) f = _ from iteratedDeriv_exp_const_mul _ _, sub_zero,
      pow_succ (-s), pow_mul]
    exact
      div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (sq_nonneg _) _) (neg_nonpos.mpr hs))
            (Real.exp_pos _).le)
          (pow_nonneg ht.le _))
        (Nat.cast_nonneg _)
  have hb := sub_nonpos.mp (hx.trans_le hr)
  rw [taylor_within_apply] at hb
  refine hb.trans_eq (Finset.sum_congr rfl (fun j _ ↦ ?_))
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc hne) (hf.of_le le_top).contDiffAt
      (Set.left_mem_uIcc)]
  rw [show iteratedDeriv j f = _ from iteratedDeriv_exp_const_mul _ _]
  simp only [sub_zero, smul_eq_mul, mul_zero, Real.exp_zero, mul_one, div_eq_mul_inv]
  ring

/-- Bound the exponentially weighted compensation on a cell by the moments
of the even Taylor majorant, using order four for the main charge in H15. -/
theorem bernstein_compensation_exp_le (P : Polynomial ℚ) (n m : ℕ) (hP : P.natDegree ≤ n) {h s : ℝ}
    (hh : 0 < h) (hs : 0 ≤ s) :
    (∫ t in 0..h, Real.exp (-s * t) * (bernsteinCompensation P n).eval (t / h)) ≤
      ∑ j ∈ Finset.range (2 * m + 1),
        ((-s) ^ j / (j.factorial : ℝ)) *
          (∑ i : Fin (n + 1),
            (↑(max 0 (-bernsteinRatCoeff P n i.val)) : ℝ) *
              (h ^ (j + 1) *
                ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) /
                  ((n + j : ℕ) + 1)))) := by
  exact
    bernstein_compensation_taylor_le P n _ hP hh
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)) _
      (fun _ ht ↦ exp_decay_le_even_taylor hs ht.1 m)

/-- Translate the log-coordinate cell to zero and replace its left-end
exponential factor by any certified upper bound. -/
theorem bernstein_compensation_shift_le (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    {l h s U : ℝ} (hh : 0 < h) (hU : Real.exp (-s * l) ≤ U) :
    (∫ v in l..l + h, Real.exp (-s * v) * (bernsteinCompensation P n).eval ((v - l) / h)) ≤
      U * ∫ t in 0..h, Real.exp (-s * t) * (bernsteinCompensation P n).eval (t / h) := by
  let g := fun v : ℝ ↦ Real.exp (-s * v) * (bernsteinCompensation P n).eval ((v - l) / h)
  have hg := intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := h) l
  rw [zero_add, add_comm h l] at hg
  change (∫ v in l..l + h, g v) ≤ _
  rw [← hg]
  simp only [g, add_sub_cancel_right]
  rw [← intervalIntegral.integral_const_mul]
  simpa only [mul_assoc] using
    (bernstein_compensation_integral_le P n hP hh (w := fun t ↦ Real.exp (-s * (t + l))) (U :=
      fun t ↦ U * Real.exp (-s * t))
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.add continuous_const)))
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      (fun t _ ↦ by
        rw [mul_add, Real.exp_add, mul_comm (Real.exp (-s * t))]
        exact mul_le_mul_of_nonneg_right hU (Real.exp_pos _).le))

/-- Bound the H15 main charge on a translated log cell by a certified
endpoint factor times the quartic Taylor moments. -/
theorem bernstein_compensation_cell_le (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    {l h s U : ℝ} (hh : 0 < h) (hs : 0 ≤ s) (hU : Real.exp (-s * l) ≤ U) :
    (∫ v in l..l + h, Real.exp (-s * v) * (bernsteinCompensation P n).eval ((v - l) / h)) ≤
      U *
        ∑ j ∈ Finset.range 5,
          ((-s) ^ j / (j.factorial : ℝ)) *
            (∑ i : Fin (n + 1),
              (↑(max 0 (-bernsteinRatCoeff P n i.val)) : ℝ) *
                (h ^ (j + 1) *
                  ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) /
                    ((n + j : ℕ) + 1)))) := by
  exact
    (bernstein_compensation_shift_le P n hP hh hU).trans
      (mul_le_mul_of_nonneg_left (bernstein_compensation_exp_le P n 2 hP hh hs)
        ((Real.exp_pos _).le.trans hU))

/-- The rational polynomial corresponding to the clipped Bernstein profile.
Its derivative can be computed before casting to the reals. -/
@[expose]
noncomputable def bernsteinRatCompensation (P : Polynomial ℚ) (n : ℕ) : Polynomial ℚ :=
  ∑ i : Fin (n + 1),
    Polynomial.C (max 0 (-bernsteinRatCoeff P n i.val)) * bernsteinPolynomial ℚ n i.val

/-- Rational clipping and real clipping give the same polynomial. -/
theorem bernstein_rat_compensation_map (P : Polynomial ℚ) (n : ℕ) :
    (bernsteinRatCompensation P n).map (Rat.castHom ℝ) = bernsteinCompensation P n := by
  simp only [bernsteinRatCompensation, bernsteinCompensation, Polynomial.map_sum,
    Polynomial.map_mul, Polynomial.map_C, Rat.coe_castHom, Rat.cast_max, Rat.cast_zero,
    Rat.cast_neg, bernsteinPolynomial, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X, Polynomial.map_natCast]

private theorem rat_compensation_degree (P : Polynomial ℚ) (n : ℕ) :
    (bernsteinRatCompensation P n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [bernsteinPolynomial, ← Polynomial.C_eq_natCast]
  have hX : (1 - Polynomial.X : Polynomial ℚ).natDegree ≤ 1 :=
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le (Polynomial.natDegree_one.trans_le (Nat.zero_le _)) Polynomial.natDegree_X.le)
  exact
    (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add
            ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_pow i.val).le)
            ((Polynomial.natDegree_pow_le_of_le _ hX).trans_eq (Nat.mul_one _)))).trans_eq
      (Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt))

/-- The normalized variation polynomial combines the compensation and its
physical derivative before any absolute values are taken. -/
@[expose]
noncomputable def bernsteinRatVariation (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) : Polynomial ℚ :=
  Polynomial.C d * bernsteinRatCompensation P n -
    Polynomial.C h⁻¹ * (bernsteinRatCompensation P n).derivative

/-- The variation polynomial can be expanded at the original Bernstein degree. -/
theorem bernstein_rat_variation_degree (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) :
    (bernsteinRatVariation P n d h).natDegree ≤ n := by
  have hc := rat_compensation_degree P n
  exact
    (Polynomial.natDegree_sub_le _ _).trans
      (max_le ((Polynomial.natDegree_C_mul_le _ _).trans hc)
        ((Polynomial.natDegree_C_mul_le _ _).trans
          ((Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hc))))

/-- Expand the signed variation at degree n before bounding its absolute
value, which preserves cancellation between compensation and derivative. -/
theorem bernstein_variation_abs_le (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) (t : Set.Icc (0 : ℝ) 1) :
    |(d : ℝ) * (bernsteinCompensation P n).eval (t : ℝ) -
          (h : ℝ)⁻¹ * (bernsteinCompensation P n).derivative.eval (t : ℝ)| ≤
      ∑ i : Fin (n + 1),
        |(bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val : ℝ)| *
          bernstein n i.val t := by
  have hv := bernstein_rat_coeff_eval _ n (bernstein_rat_variation_degree P n d h) t
  have hc := bernstein_rat_compensation_map P n
  rw [bernsteinRatVariation, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_C, Rat.coe_castHom, Rat.cast_inv, ← Polynomial.eval_map, ←
    Polynomial.eval_map, ← Polynomial.derivative_map, hc] at hv
  rw [hv]
  exact
    (Finset.abs_sum_le_sum_abs _ _).trans_eq
      (Finset.sum_congr rfl
        (fun _ _ ↦ by rw [abs_mul, abs_of_nonneg bernstein_nonneg, bernsteinRatVariation]))

/-- On a positive rational-width cell, the variation integral is bounded
by the quadratic exponential majorant integrated against the coefficient envelope. -/
theorem bernstein_variation_quadratic_le (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) (hh : 0 < (h : ℝ))
    {s : ℝ} (hs : 0 ≤ s) :
    let Q := bernsteinRatVariation P n d h
    (∫ t in 0..(h : ℝ),
        Real.exp (-s * t) *
          |(d : ℝ) * (bernsteinCompensation P n).eval (t / (h : ℝ)) -
              (h : ℝ)⁻¹ * (bernsteinCompensation P n).derivative.eval (t / (h : ℝ))|) ≤
      ∫ t in 0..(h : ℝ),
        (∑ j ∈ Finset.range 3, ((-s) ^ j / (j.factorial : ℝ)) * t ^ j) *
          ∑ i : Fin (n + 1),
            |(bernsteinRatCoeff Q n i.val : ℝ)| *
              (bernsteinPolynomial ℝ n i.val).eval (t / (h : ℝ)) := by
  let C := bernsteinCompensation P n
  let Q := bernsteinRatVariation P n d h
  let F := fun t : ℝ ↦ (t / (h : ℝ))
  have hF : Continuous F := continuous_id.div_const _
  have hV : Continuous (fun t ↦ |(d : ℝ) * C.eval (F t) - (h : ℝ)⁻¹ * C.derivative.eval (F t)|) :=
    ((continuous_const.mul (C.continuous.comp hF)).sub
        (continuous_const.mul (C.derivative.continuous.comp hF))).abs
  have hE :
    Continuous
      (fun t ↦
        ∑ i : Fin (n + 1),
          |(bernsteinRatCoeff Q n i.val : ℝ)| * (bernsteinPolynomial ℝ n i.val).eval (F t)) :=
    continuous_finsetSum _
      (fun i _ ↦ continuous_const.mul ((bernsteinPolynomial ℝ n i.val).continuous.comp hF))
  have hT : Continuous (fun t : ℝ ↦ ∑ j ∈ Finset.range 3, ((-s) ^ j / (j.factorial : ℝ)) * t ^ j) :=
    continuous_finsetSum _ (fun j _ ↦ continuous_const.mul (continuous_id.pow j))
  refine
    intervalIntegral.integral_mono_on hh.le
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hV).intervalIntegrable _
        _)
      ((hT.mul hE).intervalIntegrable _ _) ?_
  intro t ht
  let u : Set.Icc (0 : ℝ) 1 := ⟨F t, div_nonneg ht.1 hh.le, (div_le_one hh).mpr ht.2⟩
  exact
    mul_le_mul (exp_decay_le_even_taylor hs ht.1 1) (bernstein_variation_abs_le P n d h u)
      (abs_nonneg _) ((Real.exp_pos _).le.trans (exp_decay_le_even_taylor hs ht.1 1))

/-- The quadratic variation bound on a positive-width cell is a finite
sum of Bernstein moments with the absolute combined coefficients. -/
theorem bernstein_variation_moments_le (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) (hh : 0 < (h : ℝ))
    {s : ℝ} (hs : 0 ≤ s) :
    (∫ t in 0..(h : ℝ),
        Real.exp (-s * t) *
          |(d : ℝ) * (bernsteinCompensation P n).eval (t / (h : ℝ)) -
              (h : ℝ)⁻¹ * (bernsteinCompensation P n).derivative.eval (t / (h : ℝ))|) ≤
      ∑ j ∈ Finset.range 3,
        ((-s) ^ j / (j.factorial : ℝ)) *
          (∑ i : Fin (n + 1),
            |(bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val : ℝ)| *
              ((h : ℝ) ^ (j + 1) *
                ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) /
                  ((n + j : ℕ) + 1)))) := by
  let c := fun i : Fin (n + 1) ↦ |(bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val : ℝ)|
  let F := fun t : ℝ ↦ ∑ i : Fin (n + 1), c i * (bernsteinPolynomial ℝ n i.val).eval (t / (h : ℝ))
  let a := fun j : ℕ ↦ (-s) ^ j / (j.factorial : ℝ)
  have hF : Continuous F :=
    continuous_finsetSum _
      (fun i _ ↦
        continuous_const.mul
          ((bernsteinPolynomial ℝ n i.val).continuous.comp (continuous_id.div_const _)))
  have hi (j : ℕ) :
    IntervalIntegrable (fun t : ℝ ↦ a j * (t ^ j * F t)) MeasureTheory.volume 0 (h : ℝ) :=
    (continuous_const.mul ((continuous_id.pow j).mul hF)).intervalIntegrable _ _
  refine (bernstein_variation_quadratic_le P n d h hh hs).trans_eq ?_
  change (∫ t in 0..(h : ℝ), (∑ j ∈ Finset.range 3, a j * t ^ j) * F t) = _
  simp only [Finset.sum_mul, mul_assoc]
  rw [intervalIntegral.integral_finsetSum (fun j _ ↦ hi j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  refine congrArg (a j * ·) (bernstein_profile_moment hh n j c (fun t _ ↦ ?_))
  simp only [F, bernsteinPolynomial, Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_one, Polynomial.eval_X, Polynomial.eval_natCast]

/-- Bound the H15 variation charge in the physical log coordinate using
the left-end exponential bound and the quadratic moments of the envelope. -/
theorem bernstein_variation_cell_le (P : Polynomial ℚ) (n : ℕ) (d h : ℚ) (hh : 0 < (h : ℝ))
    {l s U : ℝ} (hs : 0 ≤ s) (hU : Real.exp (-s * l) ≤ U) :
    (∫ v in l..l + (h : ℝ),
        Real.exp (-s * v) *
          |(d : ℝ) * (bernsteinCompensation P n).eval ((v - l) / (h : ℝ)) -
              (h : ℝ)⁻¹ * (bernsteinCompensation P n).derivative.eval ((v - l) / (h : ℝ))|) ≤
      U *
        ∑ j ∈ Finset.range 3,
          ((-s) ^ j / (j.factorial : ℝ)) *
            (∑ i : Fin (n + 1),
              |(bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val : ℝ)| *
                ((h : ℝ) ^ (j + 1) *
                  ((n.choose i.val : ℝ) / ((n + j).choose (i.val + j) : ℝ) /
                    ((n + j : ℕ) + 1)))) := by
  let C := bernsteinCompensation P n
  let V := fun t : ℝ ↦
    |(d : ℝ) * C.eval (t / (h : ℝ)) - (h : ℝ)⁻¹ * C.derivative.eval (t / (h : ℝ))|
  let g := fun v : ℝ ↦ Real.exp (-s * v) * V (v - l)
  have hg := intervalIntegral.integral_comp_add_right (f := g) (a := (0 : ℝ)) (b := (h : ℝ)) l
  rw [zero_add, add_comm (h : ℝ) l] at hg
  change (∫ v in l..l + (h : ℝ), g v) ≤ _
  rw [← hg]
  have hf (t : ℝ) : g (t + l) = Real.exp (-s * l) * (Real.exp (-s * t) * V t) := by
    simp only [g, add_sub_cancel_right, mul_add, Real.exp_add]
    rw [mul_comm (Real.exp (-s * t)) (Real.exp (-s * l)), mul_assoc]
  simp only [hf, intervalIntegral.integral_const_mul]
  have h0 : 0 ≤ ∫ t in 0..(h : ℝ), Real.exp (-s * t) * V t :=
    intervalIntegral.integral_nonneg hh.le (fun t _ ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  exact
    (mul_le_mul_of_nonneg_right hU h0).trans
      (mul_le_mul_of_nonneg_left (bernstein_variation_moments_le P n d h hh hs)
        ((Real.exp_pos _).le.trans hU))

/-- Bound a negative exponential by applying the reciprocal Taylor bound
at one sixteenth of its rational argument and taking the sixteenth power. -/
@[expose]
def compensationExpUpper (x : ℚ) : ℚ :=
  gammaExpTaylorUpper (x / 16) ^ 16

/-- The rational endpoint factor used in the H15 calculation is valid for
every nonnegative rational exponent parameter. -/
theorem compensation_exp_upper_valid {x : ℚ} (hx : 0 ≤ x) :
    Real.exp (-(x : ℝ)) ≤ (compensationExpUpper x : ℝ) := by
  have h := gamma_exp_taylor_upper_valid (div_nonneg hx (by decide : (0 : ℚ) ≤ 16))
  have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 16
  rw [← Real.exp_natCast_mul] at hp
  have h16 : (16 : ℝ) ≠ 0 := by norm_num only
  simpa only [compensationExpUpper, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat,
    neg_div, mul_neg, mul_div_cancel₀ _ h16] using hp

/-- The Taylor-weighted Bernstein moment sum evaluated entirely in rational arithmetic. -/
@[expose]
def compensationMomentSum (n m : ℕ) (h s : ℚ) (c : Fin (n + 1) → ℚ) : ℚ :=
  ∑ j ∈ Finset.range (2 * m + 1),
    ((-s) ^ j / (j.factorial : ℚ)) *
      (∑ i : Fin (n + 1),
        c i *
          (h ^ (j + 1) *
            ((n.fast_choose i.val : ℚ) / ((n + j).fast_choose (i.val + j) : ℚ) /
              ((n + j : ℕ) + 1))))

/-- For rational cell coordinates and rate, the main charge has a fully
rational upper bound given by the endpoint factor and the quartic moment sum. -/
theorem bernstein_compensation_rat_cell_le (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    {l h s : ℚ} (hh : 0 < h) (hl : 0 ≤ l) (hs : 0 ≤ s) :
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-(s : ℝ) * v) * (bernsteinCompensation P n).eval ((v - (l : ℝ)) / (h : ℝ))) ≤
      (↑(compensationExpUpper (s * l) *
            compensationMomentSum n 2 h s (fun i ↦ max 0 (-bernsteinRatCoeff P n i.val))) :
        ℝ) := by
  have he := compensation_exp_upper_valid (mul_nonneg hs hl)
  rw [Rat.cast_mul, ← neg_mul] at he
  have hle :=
    bernstein_compensation_cell_le P n hP (Rat.cast_pos.mpr hh) (Rat.cast_nonneg.mpr hs) he
  simpa only [compensationMomentSum, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, ← Nat.choose_eq_fast_choose] using
    hle

/-- For rational cell coordinates and rate, the variation charge has a
rational upper bound given by the endpoint factor and the quadratic moment sum. -/
theorem bernstein_variation_rat_cell_le (P : Polynomial ℚ) (n : ℕ) (d : ℚ) {l h s : ℚ} (hh : 0 < h)
    (hl : 0 ≤ l) (hs : 0 ≤ s) :
    (∫ v in (l : ℝ)..(l : ℝ) + (h : ℝ),
        Real.exp (-(s : ℝ) * v) *
          |(d : ℝ) * (bernsteinCompensation P n).eval ((v - (l : ℝ)) / (h : ℝ)) -
              (h : ℝ)⁻¹ * (bernsteinCompensation P n).derivative.eval ((v - (l : ℝ)) / (h : ℝ))|) ≤
      (↑(compensationExpUpper (s * l) *
            compensationMomentSum n 1 h s
              (fun i ↦ |bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val|)) :
        ℝ) := by
  have he := compensation_exp_upper_valid (mul_nonneg hs hl)
  rw [Rat.cast_mul, ← neg_mul] at he
  have hle := bernstein_variation_cell_le P n d h (Rat.cast_pos.mpr hh) (Rat.cast_nonneg.mpr hs) he
  simpa only [compensationMomentSum, Rat.cast_mul, Rat.cast_sum, Rat.cast_div, Rat.cast_pow,
    Rat.cast_neg, Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Rat.cast_abs,
    ← Nat.choose_eq_fast_choose] using hle

/-- Differentiating a Bernstein sum of degree `n + 1` uses adjacent coefficient
differences in degree `n`. This avoids converting the profile to powers. -/
theorem bernstein_derivative_neighbors {R : Type*} [CommRing R] (n : ℕ) (c : ℕ → R) :
    (∑ i ∈ Finset.range (n + 2), Polynomial.C (c i) * bernsteinPolynomial R (n + 1) i).derivative =
      ((n + 1 : ℕ) : Polynomial R) *
        ∑ i ∈ Finset.range (n + 1), Polynomial.C (c (i + 1) - c i) * bernsteinPolynomial R n i := by
  simp only [Polynomial.derivative_sum, Polynomial.derivative_C_mul]
  rw [Finset.sum_range_succ']
  simp only [bernsteinPolynomial.derivative_succ, bernsteinPolynomial.derivative_zero,
    Nat.add_sub_cancel, mul_sub, mul_neg, ← mul_assoc, Finset.sum_sub_distrib, Polynomial.C_sub,
    sub_mul]
  simp only [Finset.mul_sum, ← mul_assoc]
  have hz : bernsteinPolynomial R n (n + 1) = 0 :=
    bernsteinPolynomial.eq_zero_of_lt R (Nat.lt_succ_self n)
  let f := fun i ↦ Polynomial.C (c i) * (↑(n + 1 : ℕ) : Polynomial R) * bernsteinPolynomial R n i
  have hshift :
    (∑ i ∈ Finset.range (n + 1), f (i + 1)) + f 0 = ∑ i ∈ Finset.range (n + 1), f i := by
    rw [← Finset.sum_range_succ', Finset.sum_range_succ]
    simp only [f, hz, mul_zero, add_zero]
  rw [neg_mul, ← sub_eq_add_neg, sub_sub, hshift]
  simp only [f, mul_comm (↑(n + 1 : ℕ) : Polynomial R)]

/-- Multiply a Bernstein basis polynomial by the new degree and express it
using the two adjacent basis polynomials at that degree. -/
theorem bernstein_raise_one {R : Type*} [CommRing R] (n i : ℕ) (hi : i ≤ n) :
    ((n + 1 : ℕ) : Polynomial R) * bernsteinPolynomial R n i =
      ((n + 1 - i : ℕ) : Polynomial R) * bernsteinPolynomial R (n + 1) i +
        ((i + 1 : ℕ) : Polynomial R) * bernsteinPolynomial R (n + 1) (i + 1) := by
  have h₁ :
    ((n + 1 - i : ℕ) : Polynomial R) * ((n + 1).choose i : Polynomial R) =
      (n + 1 : ℕ) * (n.choose i : Polynomial R) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact
      congrArg (fun k : ℕ ↦ (k : Polynomial R))
        (by simpa only [Nat.mul_comm] using (Nat.choose_mul_succ_eq n i).symm :
          (n + 1 - i) * (n + 1).choose i = (n + 1) * n.choose i)
  have h₂ :
    ((i + 1 : ℕ) : Polynomial R) * ((n + 1).choose (i + 1) : Polynomial R) =
      (n + 1 : ℕ) * (n.choose i : Polynomial R) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul]
    exact
      congrArg (fun k : ℕ ↦ (k : Polynomial R))
        (by simpa only [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n i).symm :
          (i + 1) * (n + 1).choose (i + 1) = (n + 1) * n.choose i)
  have hd : n + 1 - i = n - i + 1 := Nat.succ_sub hi
  simp only [bernsteinPolynomial, ← mul_assoc]
  rw [h₁, h₂, hd, Nat.add_sub_add_right]
  simp only [pow_succ]
  ring

/-- The degree-preserving Bernstein coefficient of the derivative is the
weighted sum of its two adjacent differences. The outer weights vanish at the ends. -/
@[expose]
def bernsteinDerivativeCoeff {R : Type*} [CommRing R] (m : ℕ) (c : ℕ → R) (i : ℕ) : R :=
  ((m - i : ℕ) : R) * (c (i + 1) - c i) + (i : R) * (c i - c (i - 1))

/-- Differentiate a Bernstein sum directly in its original degree. -/
theorem bernstein_derivative_same_degree {R : Type*} [CommRing R] (n : ℕ) (c : ℕ → R) :
    (∑ i ∈ Finset.range (n + 1), Polynomial.C (c i) * bernsteinPolynomial R n i).derivative =
      ∑ i ∈ Finset.range (n + 1),
        Polynomial.C (bernsteinDerivativeCoeff n c i) * bernsteinPolynomial R n i := by
  cases n with
  | zero =>
    simp only [Nat.zero_add, Finset.sum_range_one, bernsteinDerivativeCoeff, Nat.sub_zero,
      Nat.cast_zero, zero_mul, add_zero, map_zero, bernsteinPolynomial, Nat.choose_zero_right,
      Nat.cast_one, pow_zero, mul_one, Polynomial.derivative_C]
  | succ n =>
    rw [bernstein_derivative_neighbors]
    let A := fun i ↦
      Polynomial.C (c (i + 1) - c i) * ((n + 1 - i : ℕ) : Polynomial R) *
        bernsteinPolynomial R (n + 1) i
    let B := fun i ↦
      Polynomial.C (c i - c (i - 1)) * (i : Polynomial R) * bernsteinPolynomial R (n + 1) i
    have hA : (∑ i ∈ Finset.range (n + 2), A i) = ∑ i ∈ Finset.range (n + 1), A i := by
      rw [Finset.sum_range_succ]
      simp only [A, Nat.sub_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hB : (∑ i ∈ Finset.range (n + 2), B i) = ∑ i ∈ Finset.range (n + 1), B (i + 1) := by
      rw [Finset.sum_range_succ']
      simp only [B, Nat.cast_zero, mul_zero, zero_mul, add_zero]
    have hsum :
      (∑ i ∈ Finset.range (n + 2),
          Polynomial.C (bernsteinDerivativeCoeff (n + 1) c i) * bernsteinPolynomial R (n + 1) i) =
        ∑ i ∈ Finset.range (n + 2), (A i + B i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [A, B, bernsteinDerivativeCoeff, Polynomial.C_add, Polynomial.C_mul,
        Polynomial.C_eq_natCast, add_mul]
      ring
    rw [hsum, Finset.sum_add_distrib, hA, hB, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_left_comm, ← mul_assoc, mul_assoc (Polynomial.C _),
      bernstein_raise_one n i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
    simp only [A, B, Nat.add_sub_cancel, mul_add, mul_assoc]

/-- Recover a bounded-degree rational polynomial from its Bernstein coefficients. -/
private theorem bernstein_rat_expand (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) :
    P =
      ∑ i : Fin (n + 1),
        Polynomial.C (bernsteinRatCoeff P n i.val) * bernsteinPolynomial ℚ n i.val := by
  apply Polynomial.map_injective (f := Rat.castHom ℝ) Rat.cast_injective
  apply Polynomial.eq_of_infinite_eval_eq
  refine (Set.Icc_infinite (zero_lt_one : (0 : ℝ) < 1)).mono ?_
  intro t ht
  change (P.map (Rat.castHom ℝ)).eval t = _
  simp only [Polynomial.eval_map, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Rat.coe_castHom,
    bernsteinPolynomial, Polynomial.map_natCast, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_one, Polynomial.map_X, Polynomial.eval_natCast, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
  simpa only [bernstein_apply] using bernstein_rat_coeff_eval P n hP ⟨t, ht⟩

/-- The signed variation coefficient computed directly from clipped neighbors. -/
@[expose]
def bernsteinVariationDirect (n i : ℕ) (d h : ℚ) (c : ℕ → ℚ) : ℚ :=
  d * c i - h⁻¹ * bernsteinDerivativeCoeff n c i

/-- The direct variation coefficient equals the coefficient of the analytic
variation polynomial at every index in the Bernstein basis. -/
theorem bernstein_variation_direct_eq (P : Polynomial ℚ) (n : ℕ) (i : Fin (n + 1)) (d h : ℚ) :
    bernsteinRatCoeff (bernsteinRatVariation P n d h) n i.val =
      bernsteinVariationDirect n i.val d h (fun j ↦ max 0 (-bernsteinRatCoeff P n j)) := by
  let c := fun j ↦ max 0 (-bernsteinRatCoeff P n j)
  let v := fun j : Fin (n + 1) ↦ bernsteinVariationDirect n j.val d h c
  let V := bernsteinRatVariation P n d h
  have hd :
    (bernsteinRatCompensation P n).derivative =
      ∑ j : Fin (n + 1),
        Polynomial.C (bernsteinDerivativeCoeff n c j.val) * bernsteinPolynomial ℚ n j.val := by
    simpa only [bernsteinRatCompensation, ← Fin.sum_univ_eq_sum_range, c] using
      bernstein_derivative_same_degree n c
  have hv : V = ∑ j : Fin (n + 1), Polynomial.C (v j) * bernsteinPolynomial ℚ n j.val := by
    change bernsteinRatVariation P n d h = _
    rw [bernsteinRatVariation, hd]
    simp only [bernsteinRatCompensation, Finset.mul_sum, ← Finset.sum_sub_distrib, v,
      bernsteinVariationDirect, c, Polynomial.C_sub, Polynomial.C_mul, sub_mul, mul_assoc]
  have he := (bernstein_rat_expand V n (bernstein_rat_variation_degree P n d h)).symm.trans hv
  have hz :
    ∑ j : Fin (n + 1), (bernsteinRatCoeff V n j.val - v j) • bernsteinPolynomial ℚ n j.val = 0 := by
    simp only [Polynomial.smul_eq_C_mul, Polynomial.C_sub, sub_mul, Finset.sum_sub_distrib, he,
      sub_self]
  exact
    sub_eq_zero.mp
      ((linearIndependent_iff'.mp (bernsteinPolynomial.linearIndependent n)) Finset.univ _ hz i
        (Finset.mem_univ i))

/-- Compute one power coefficient of a Bernstein profile from its rational
coefficients, using the binomial expansion of each basis term. -/
@[expose]
def bernsteinPowerCoeff (n k : ℕ) (c : Fin (n + 1) → ℚ) : ℚ :=
  ∑ i : Fin (n + 1),
    if i.val ≤ k then
      c i * (Nat.fast_choose n i.val : ℚ) *
        ((-1 : ℚ) ^ (k - i.val) * (Nat.fast_choose (n - i.val) (k - i.val) : ℚ))
    else 0

private theorem one_sub_X_pow_coeff (n k : ℕ) :
    ((1 - Polynomial.X : Polynomial ℚ) ^ n).coeff k = (-1 : ℚ) ^ k * (Nat.fast_choose n k : ℚ) := by
  rw [← neg_sub, neg_pow]
  have hneg : Polynomial.C (-1 : ℚ) = -1 := by rw [Polynomial.C_neg, Polynomial.C_1]
  rw [← hneg, ← Polynomial.C_pow, Polynomial.coeff_C_mul, sub_eq_add_neg, ← hneg,
    Polynomial.coeff_X_add_C_pow, ← Nat.choose_eq_fast_choose]
  by_cases hk : k ≤ n
  · have he : n + (n - k) = k + 2 * (n - k) := by
      calc
        _ = ((n - k) + k) + (n - k) := by rw [Nat.sub_add_cancel hk]
        _ = _ := by ring
    rw [← mul_assoc, ← pow_add, he, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero, mul_zero, mul_zero, mul_zero]

/-- The clipped polynomial has the directly computed rational power coefficients. -/
theorem bernstein_compensation_power_coeff (P : Polynomial ℚ) (n k : ℕ) :
    (bernsteinRatCompensation P n).coeff k =
      bernsteinPowerCoeff n k (fun i ↦ max 0 (-bernsteinRatCoeff P n i.val)) := by
  simp only [bernsteinRatCompensation, bernsteinPowerCoeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [bernsteinPolynomial, ← Polynomial.C_eq_natCast, mul_assoc (Polynomial.C (n.choose i.val : ℚ)),
    Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul',
    one_sub_X_pow_coeff]
  by_cases hk : i.val ≤ k
  · rw [ite_eq_left hk, ite_eq_left hk, ← Nat.choose_eq_fast_choose, mul_assoc]
  · rw [ite_eq_right hk, ite_eq_right hk, mul_zero, mul_zero]

/-- Compute the signed variation Bernstein coefficient via the power
coefficients of the clipped profile and the rational differentiation rule. -/
@[expose]
def bernsteinVariationCoeff (n i : ℕ) (d h : ℚ) (c : Fin (n + 1) → ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ≤ i then
      (d * bernsteinPowerCoeff n k c - h⁻¹ * (bernsteinPowerCoeff n (k + 1) c * (k + 1 : ℕ))) *
        ((Nat.fast_choose i k : ℚ) / (Nat.fast_choose n k : ℚ))
    else 0

/-- The arithmetic variation coefficient equals the analytic one before
taking the absolute value in the H15 upper envelope. -/
theorem bernstein_variation_coeff_eq (P : Polynomial ℚ) (n i : ℕ) (d h : ℚ) :
    bernsteinRatCoeff (bernsteinRatVariation P n d h) n i =
      bernsteinVariationCoeff n i d h (fun j ↦ max 0 (-bernsteinRatCoeff P n j.val)) := by
  simp only [bernsteinRatCoeff, bernsteinVariationCoeff, bernsteinRatVariation,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_derivative,
    bernstein_compensation_power_coeff, Nat.cast_add, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : k ≤ i
  · rw [ite_eq_left hk]
  · simp only [ite_eq_right hk, ← Nat.choose_eq_fast_choose,
      Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero, zero_div, mul_zero]

/-- Compute the power coefficients of the combined variation once for all
Bernstein coefficients in a cell. -/
@[expose]
def bernsteinVariationPowerRow (n : ℕ) (d h : ℚ) (c : Fin (n + 1) → ℚ) : Array ℚ :=
  let p := Array.ofFn (fun k : Fin (n + 2) ↦ bernsteinPowerCoeff n k.val c)
  Array.ofFn
    (fun k : Fin (n + 1) ↦ d * p[k.val]?.getD 0 - h⁻¹ * (p[k.val + 1]?.getD 0 * (k.val + 1 : ℕ)))

/-- Convert one coefficient from the shared power row of the variation. -/
@[expose]
def bernsteinVariationFromRow (n i : ℕ) (row : Array ℚ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1),
    if k ≤ i then row[k]?.getD 0 * ((Nat.fast_choose i k : ℚ) / (Nat.fast_choose n k : ℚ)) else 0

/-- The shared power row gives the same variation coefficient as direct conversion. -/
theorem bernstein_variation_row_eq (n i : ℕ) (d h : ℚ) (c : Fin (n + 1) → ℚ) :
    bernsteinVariationFromRow n i (bernsteinVariationPowerRow n d h c) =
      bernsteinVariationCoeff n i d h c := by
  simp only [bernsteinVariationFromRow, bernsteinVariationCoeff, bernsteinVariationPowerRow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk₀ := Finset.mem_range.mp hk
  have hk₁ := Nat.lt_succ_of_lt hk₀
  have hk₂ := Nat.succ_lt_succ hk₀
  simp only [getElem?_def, Array.size_ofFn, hk₀, hk₁, hk₂, dite_eq_left, Array.getElem_ofFn,
    Option.getD_some]

/-- A single rational cell bounds the exponentially weighted negative part
by the clipped Bernstein mean and a left-endpoint weight bound. -/
theorem weighted_negative_bernstein_cell (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) {s : ℝ}
    (hs : 0 ≤ s) {l r : ℚ} (hlr : l < r) (E : ℚ) (hE : Real.exp (-s * (l : ℝ)) ≤ (E : ℝ)) :
    let Q := P.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l)
    (∫ t in (l : ℝ)..(r : ℝ), Real.exp (-s * t) * max 0 (-P.eval₂ (Rat.castHom ℝ) t)) ≤
      ((E * ((r - l) * ((∑ i : Fin (n + 1), max 0 (-bernsteinRatCoeff Q n i)) / ((n : ℚ) + 1)))) :
        ℚ) := by
  intro Q
  let w : ℝ := (r : ℝ) - (l : ℝ)
  have hw : 0 < w := sub_pos.mpr (Rat.cast_lt.mpr hlr)
  let F := fun t : ℝ ↦ Real.exp (-s * t) * max 0 (-P.eval₂ (Rat.castHom ℝ) t)
  let C := fun t : ℝ ↦ (bernsteinCompensation Q n).eval (t / w)
  have hF : Continuous F := by
    unfold F; fun_prop
  have hC : Continuous C := (bernsteinCompensation Q n).continuous.comp (continuous_id.div_const w)
  have hc := intervalIntegral.integral_comp_add_right (f := F) (a := 0) (b := w) (l : ℝ)
  rw [zero_add, show w + (l : ℝ) = r from sub_add_cancel _ _] at hc
  change (∫ t in (l : ℝ)..(r : ℝ), F t) ≤ _
  rw [← hc]
  have hFt : Continuous (fun t : ℝ ↦ F (t + l)) := hF.comp (continuous_id.add continuous_const)
  have hmono :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hw.le (hFt.intervalIntegrable 0 w)
      ((hC.const_mul (E : ℝ)).intervalIntegrable 0 w)
      (fun (t : ℝ) (ht : t ∈ Set.Icc 0 w) ↦ by
        let u : Set.Icc (0 : ℝ) 1 := ⟨t / w, div_nonneg ht.1 hw.le, (div_le_one hw).mpr ht.2⟩
        have hnc := bernstein_affine_compensation_nonneg P n hP l r u
        have heval : ((r - l : ℚ) : ℝ) * (u : ℝ) + (l : ℝ) = t + (l : ℝ) := by
          rw [Rat.cast_sub]
          change w * (t / w) + (l : ℝ) = _
          rw [mul_comm w, div_mul_cancel₀ _ hw.ne']
        rw [heval] at hnc
        have hmax : max 0 (-P.eval₂ (Rat.castHom ℝ) (t + l)) ≤ C t :=
          max_le hnc.1
            (neg_le_iff_add_nonneg.mpr
              (by
                rw [add_comm (C t)]
                exact hnc.2))
        exact
          mul_le_mul
            ((Real.exp_le_exp.mpr
                  (mul_le_mul_of_nonpos_left (le_add_of_nonneg_left ht.1)
                    (neg_nonpos.mpr hs))).trans
              hE)
            hmax (le_max_left _ _) ((Real.exp_nonneg _).trans hE))
  refine hmono.trans_eq ?_
  rw [intervalIntegral.integral_const_mul]
  have hm := bernstein_compensation_moment Q n 0 hw
  simp only [pow_zero, one_mul, Nat.add_zero, zero_add, pow_one] at hm
  change (E : ℝ) * (∫ t in 0..w, (bernsteinCompensation Q n).eval (t / w)) = _
  rw [hm]
  simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_sum, Rat.cast_max, Rat.cast_zero,
    Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Rat.cast_one]
  congr 1
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : (n.choose (i : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (Nat.le_of_lt_succ i.isLt)).ne'
  rw [div_self hi]
  dsimp only [w]
  ring

/-- Sum the clipped Bernstein charges along an increasing rational partition
to bound the full weighted negative moment. -/
theorem weighted_negative_bernstein (P : Polynomial ℚ) (N n : ℕ) (hP : P.natDegree ≤ n) {s : ℝ}
    (hs : 0 ≤ s) (p e : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1))
    (he : ∀ j < N, Real.exp (-s * (p j : ℝ)) ≤ (e j : ℝ)) :
    (∫ t in (p 0 : ℝ)..(p N : ℝ), Real.exp (-s * t) * max 0 (-P.eval₂ (Rat.castHom ℝ) t)) ≤
      ((∑ j ∈ Finset.range N,
          e j *
            ((p (j + 1) - p j) *
              ((∑ i : Fin (n + 1),
                  max 0
                    (-bernsteinRatCoeff
                        (P.comp
                          (Polynomial.C (p (j + 1) - p j) * Polynomial.X + Polynomial.C (p j)))
                        n i)) /
                ((n : ℚ) + 1)))) :
        ℚ) := by
  have hf : Continuous (fun t : ℝ ↦ Real.exp (-s * t) * max 0 (-P.eval₂ (Rat.castHom ℝ) t)) := by
    fun_prop
  rw [←
    intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ ↦ hf.intervalIntegrable (p j : ℝ) (p (j + 1) : ℝ)),
    Rat.cast_sum]
  exact
    Finset.sum_le_sum fun j hj ↦
      weighted_negative_bernstein_cell P n hP hs (hp j (Finset.mem_range.mp hj)) (e j)
        (he j (Finset.mem_range.mp hj))

end PseudoPrime.Analysis
