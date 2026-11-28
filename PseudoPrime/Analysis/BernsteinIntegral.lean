/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.Analysis.BernsteinBounds
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.Ring

/-! # Integrating absolute Bernstein coefficient bounds -/

namespace PseudoPrime.Analysis

/-- Every Bernstein basis polynomial of degree `n` has integral `1/(n+1)`. -/
public theorem bernstein_basis_integral (n k : ℕ) (hk : k ≤ n) :
    (∫ x : ℝ in 0..1, (n.choose k : ℝ) * x ^ k * (1 - x) ^ (n - k)) = 1 / ((n : ℝ) + 1) := by
  let m := n - k
  have hm : k + m = n := Nat.add_sub_of_le hk
  let f := fun x : ℝ ↦ x ^ k * (1 - x) ^ m
  have hf : Continuous f := by
    unfold f; fun_prop
  have hc :=
    Complex.ofRealCLM.intervalIntegral_comp_comm
      (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
  change (∫ x : ℝ in 0..1, Complex.ofReal (f x)) = Complex.ofReal (∫ x : ℝ in 0..1, f x) at hc
  have hb :=
    Complex.betaIntegral_eq_Gamma_mul_div ((k : ℂ) + 1) ((m : ℂ) + 1)
      (by
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
      (by
        simp only [Complex.add_re, Complex.natCast_re, Complex.one_re]; positivity)
  have hsum : (k : ℂ) + 1 + ((m : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) + 1 := by
    have h := congrArg (fun j : ℕ ↦ (j : ℂ)) hm
    simp only [Nat.cast_add] at h
    simp only [Nat.cast_add, Nat.cast_one]
    linear_combination h
  rw [hsum, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial, Complex.betaIntegral] at hb
  simp only [add_sub_cancel_right, Complex.cpow_natCast] at hb
  have he :
    (∫ x : ℝ in 0..1, (x : ℂ) ^ k * (1 - (x : ℂ)) ^ m) = Complex.ofReal (∫ x : ℝ in 0..1, f x) := by
    rw [← hc]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [f, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one]
  rw [he] at hb
  have hre := congrArg Complex.re hb
  have hcast :
    ((k.factorial : ℂ) * (m.factorial : ℂ) / ((n + 1).factorial : ℂ)) =
      Complex.ofReal ((k.factorial : ℝ) * (m.factorial : ℝ) / ((n + 1).factorial : ℝ)) := by
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [hcast, Complex.ofReal_re, Complex.ofReal_re] at hre
  have hfac := congrArg (fun j : ℕ ↦ (j : ℝ)) (Nat.choose_mul_factorial_mul_factorial hk)
  simp only [Nat.cast_mul] at hfac
  change (∫ x : ℝ in 0..1, (n.choose k : ℝ) * x ^ k * (1 - x) ^ m) = _
  simp only [mul_assoc, intervalIntegral.integral_const_mul]
  change (n.choose k : ℝ) * (∫ x : ℝ in 0..1, f x) = _
  rw [hre, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have hp : (0 : ℝ) < n.factorial := Nat.cast_pos.mpr (Nat.factorial_pos n)
  field_simp [hp.ne', (show (n : ℝ) + 1 ≠ 0 by positivity)]
  simpa only [m, mul_assoc] using hfac

/-- On the unit interval, the absolute integral is bounded by the mean absolute
Bernstein coefficient. The representation need only hold on the interval. -/
public theorem bernstein_abs_integral (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 0 1)) (n : ℕ)
    (c : Fin (n + 1) → ℝ)
    (hrep : ∀ x : Set.Icc (0 : ℝ) 1, f x = ∑ k : Fin (n + 1), c k * bernstein n k x) :
    (∫ x : ℝ in 0..1, |f x|) ≤ (∑ k : Fin (n + 1), |c k|) / ((n : ℝ) + 1) := by
  let g := fun (k : Fin (n + 1)) (x : ℝ) ↦
    |c k| * ((n.choose k : ℝ) * x ^ (k : ℕ) * (1 - x) ^ (n - (k : ℕ)))
  have hg (k : Fin (n + 1)) : Continuous (g k) := by
    unfold g; fun_prop
  have hi : IntervalIntegrable (fun x ↦ ∑ k : Fin (n + 1), g k x) MeasureTheory.volume 0 1 :=
    (continuous_finsetSum _ (fun k _ ↦ hg k)).intervalIntegrable _ _
  have hfi : IntervalIntegrable (fun x ↦ |f x|) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hf.abs
  have h :=
    intervalIntegral.integral_mono_on zero_le_one hfi hi
      (fun x hx ↦ by
        rw [show f x = _ from hrep ⟨x, hx⟩, ← Real.norm_eq_abs]
        refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun k _ ↦ ?_))
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg bernstein_nonneg,
          bernstein_apply])
  refine h.trans_eq ?_
  rw [intervalIntegral.integral_finsetSum (fun k _ ↦ (hg k).intervalIntegrable _ _), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [show
      (∫ x : ℝ in 0..1, g k x) =
        |c k| * (∫ x : ℝ in 0..1, (n.choose k : ℝ) * x ^ (k : ℕ) * (1 - x) ^ (n - (k : ℕ)))
      from intervalIntegral.integral_const_mul _ _,
    bernstein_basis_integral n k (Nat.le_of_lt_succ k.isLt), mul_one_div]

/-- On a cell, freeze an exponential at its larger endpoint value and integrate
the absolute Bernstein coefficient majorant. -/
public theorem exp_abs_bernstein_cell (f : ℝ → ℝ) (hf : Continuous f) {a l r : ℝ} (hlr : l < r)
    (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hrep :
      ∀ x : Set.Icc (0 : ℝ) 1, f ((r - l) * x + l) = ∑ k : Fin (n + 1), c k * bernstein n k x) :
    (∫ x in l..r, Real.exp (a * x) * |f x|) ≤
      Real.exp (max (a * l) (a * r)) *
        ((r - l) * ((∑ k : Fin (n + 1), |c k|) / ((n : ℝ) + 1))) := by
  have hg : Continuous (fun x ↦ Real.exp (a * x) * |f x|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.abs
  have hM : Continuous (fun x ↦ Real.exp (max (a * l) (a * r)) * |f x|) := hf.abs.const_mul _
  have hm (x : ℝ) (hx : x ∈ Set.Icc l r) : a * x ≤ max (a * l) (a * r) := by
    rcases le_total 0 a with ha | ha
    · exact (mul_le_mul_of_nonneg_left hx.2 ha).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hx.1 ha).trans (le_max_left _ _)
  have h :=
    intervalIntegral.integral_mono_on hlr.le (hg.intervalIntegrable (μ := MeasureTheory.volume) l r)
      (hM.intervalIntegrable l r)
      (fun x hx ↦ mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hm x hx)) (abs_nonneg _))
  rw [intervalIntegral.integral_const_mul] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hd := sub_pos.mpr hlr
  have hcv := intervalIntegral.integral_comp_mul_add (f := fun x ↦ |f x|) (a := 0) (b := 1) hd.ne' l
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel, smul_eq_mul] at hcv
  have he : (∫ x in l..r, |f x|) = (r - l) * ∫ x : ℝ in 0..1, |f ((r - l) * x + l)| := by
    rw [hcv, ← mul_assoc, mul_inv_cancel₀ hd.ne', one_mul]
  rw [he]
  have haff : Continuous (fun x : ℝ ↦ (r - l) * x + l) := by fun_prop
  exact
    mul_le_mul_of_nonneg_left (bernstein_abs_integral _ (hf.comp haff).continuousOn n c hrep) hd.le

/-- A decreasing exponential attains its maximum at the left endpoint. -/
public theorem weighted_abs_bernstein_cell (f : ℝ → ℝ) (hf : Continuous f) {a l r : ℝ} (ha : 0 ≤ a)
    (hlr : l < r) (n : ℕ) (c : Fin (n + 1) → ℝ)
    (hrep :
      ∀ x : Set.Icc (0 : ℝ) 1, f ((r - l) * x + l) = ∑ k : Fin (n + 1), c k * bernstein n k x) :
    (∫ x in l..r, Real.exp (-a * x) * |f x|) ≤
      Real.exp (-a * l) * ((r - l) * ((∑ k : Fin (n + 1), |c k|) / ((n : ℝ) + 1))) := by
  simpa only [max_eq_left (mul_le_mul_of_nonpos_left hlr.le (neg_nonpos.mpr ha))] using
    exp_abs_bernstein_cell (a := -a) f hf hlr n c hrep

/-- A finite partition bounds the weighted absolute integral by a sum of cell charges.
The exponential upper bounds may be supplied as rational certificates. -/
public theorem weighted_abs_bernstein_partition (f : ℝ → ℝ) (hf : Continuous f) {a : ℝ} (ha : 0 ≤ a)
    (N n : ℕ) (p : ℕ → ℝ) (c : ℕ → Fin (n + 1) → ℝ) (e : ℕ → ℝ) (hp : ∀ j < N, p j < p (j + 1))
    (he : ∀ j < N, Real.exp (-a * p j) ≤ e j)
    (hrep :
      ∀ j < N,
        ∀ x : Set.Icc (0 : ℝ) 1,
          f ((p (j + 1) - p j) * x + p j) = ∑ k : Fin (n + 1), c j k * bernstein n k x) :
    (∫ x in p 0..p N, Real.exp (-a * x) * |f x|) ≤
      ∑ j ∈ Finset.range N,
        e j * ((p (j + 1) - p j) * ((∑ k : Fin (n + 1), |c j k|) / ((n : ℝ) + 1))) := by
  have h : Continuous (fun x ↦ Real.exp (-a * x) * |f x|) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hf.abs
  rw [←
    intervalIntegral.sum_integral_adjacent_intervals
      (fun j _ ↦ h.intervalIntegrable (p j) (p (j + 1)))]
  apply Finset.sum_le_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  refine (weighted_abs_bernstein_cell f hf ha (hp j hj') n (c j) (hrep j hj')).trans ?_
  apply mul_le_mul_of_nonneg_right (he j hj')
  exact
    mul_nonneg (sub_nonneg.mpr (hp j hj').le)
      (div_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _))
        (add_nonneg (Nat.cast_nonneg _) zero_le_one))

/-- Degree elevation expresses a monomial by Bernstein coefficients given by
ratios of binomial coefficients. -/
private theorem monomial_bernstein (n k : ℕ) (hk : k ≤ n) (x : Set.Icc (0 : ℝ) 1) :
    (x : ℝ) ^ k =
      ∑ j : Fin (n + 1), ((Nat.choose j k : ℝ) / (Nat.choose n k : ℝ)) * bernstein n j x := by
  let t : ℝ := x
  let f := fun j : ℕ ↦
    ((Nat.choose j k : ℝ) / (Nat.choose n k : ℝ)) *
      ((Nat.choose n j : ℝ) * t ^ j * (1 - t) ^ (n - j))
  have hnz : (Nat.choose n k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr ((Nat.choose_pos hk).ne')
  simp only [bernstein_apply]
  change t ^ k = ∑ j : Fin (n + 1), f j.val
  rw [Fin.sum_univ_eq_sum_range]
  have hsub : Finset.Ico k (n + 1) ⊆ Finset.range (n + 1) := fun j hj ↦
    Finset.mem_range.mpr (Finset.mem_Ico.mp hj).2
  rw [← Finset.sum_subset hsub]
  swap
  · intro j hj hnot
    have hjk : j < k := lt_of_not_ge (fun h ↦ hnot (Finset.mem_Ico.mpr ⟨h, Finset.mem_range.mp hj⟩))
    simp only [f, Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, zero_div, zero_mul]
  rw [Finset.sum_Ico_eq_sum_range]
  have hlen : n + 1 - k = n - k + 1 := by omega
  rw [hlen]
  have he (j : ℕ) :
    f (k + j) = t ^ k * (t ^ j * (1 - t) ^ (n - k - j) * ((n - k).choose j : ℝ)) := by
    have hcomb :=
      congrArg (fun a : ℕ ↦ (a : ℝ)) (Nat.choose_mul (n := n) (k := k + j) (Nat.le_add_right k j))
    simp only [Nat.cast_mul, Nat.add_sub_cancel_left] at hcomb
    have hsub' : n - (k + j) = n - k - j := (Nat.sub_sub n k j).symm
    simp only [f, hsub', pow_add]
    field_simp [hnz]
    linear_combination (t ^ k * t ^ j * (1 - t) ^ (n - k - j)) * hcomb
  simp only [he, ← Finset.mul_sum, ← add_pow, add_sub_cancel, one_pow, mul_one]

/-- Bernstein coefficients of a rational polynomial, padded to degree `n`. -/
@[expose]
public noncomputable def bernsteinRatCoeff (P : Polynomial ℚ) (n j : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), P.coeff k * ((Nat.fast_choose j k : ℚ) / (Nat.fast_choose n k : ℚ))

/-- The rational Bernstein conversion is valid with an upper bound for the degree. -/
public theorem bernstein_rat_coeff_eval (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n)
    (x : Set.Icc (0 : ℝ) 1) :
    P.eval₂ (Rat.castHom ℝ) x =
      ∑ j : Fin (n + 1), (bernsteinRatCoeff P n j : ℝ) * bernstein n j x := by
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hP)]
  simp only [Rat.coe_castHom, bernsteinRatCoeff, Rat.cast_sum, Rat.cast_mul, Rat.cast_div,
    Rat.cast_natCast, ← Nat.choose_eq_fast_choose, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [monomial_bernstein n k (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) x, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ ↦ by rw [mul_assoc])

/-- Expand one affine power by the binomial theorem and select its coefficient. -/
private theorem coeff_affine_pow (l w : ℚ) (j k : ℕ) :
    ((Polynomial.C w * Polynomial.X + Polynomial.C l) ^ j).coeff k =
      w ^ k * ((j.choose k : ℚ) * l ^ (j - k)) := by
  rw [add_pow, Polynomial.finsetSum_coeff]
  have hf (i : ℕ) :
    (((Polynomial.C w * Polynomial.X) ^ i * Polynomial.C l ^ (j - i)) *
            (j.choose i : Polynomial ℚ)).coeff
        k =
      if i = k then w ^ i * l ^ (j - i) * (j.choose i : ℚ) else 0 := by
    rw [mul_pow, ← Polynomial.C_pow, ← Polynomial.C_pow, ← Polynomial.C_eq_natCast]
    have he :
      Polynomial.C (w ^ i) * Polynomial.X ^ i * Polynomial.C (l ^ (j - i)) *
          Polynomial.C (j.choose i : ℚ) =
        Polynomial.C (w ^ i * l ^ (j - i) * (j.choose i : ℚ)) * Polynomial.X ^ i := by
      rw [Polynomial.C_mul, Polynomial.C_mul]
      ring
    rw [he, Polynomial.coeff_C_mul_X_pow]
    simp only [eq_comm (a := k)]
  simp only [hf]
  by_cases h : k ≤ j
  · rw [Finset.sum_eq_single k]
    · rw [ite_eq_left rfl]
      ring
    · intro i _ hi
      rw [ite_eq_right hi]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le h))).elim
  · have hjk := Nat.lt_of_not_ge h
    rw [Nat.choose_eq_zero_of_lt hjk, Nat.cast_zero, zero_mul, mul_zero]
    apply Finset.sum_eq_zero
    intro i hi
    exact ite_eq_right (Nat.ne_of_lt ((Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans_lt hjk))

/-- The coefficient of a rational affine transform is computed by a binomial sum. -/
public theorem rational_affine_coeff (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) (l w : ℚ)
    (k : ℕ) :
    (P.comp (Polynomial.C w * Polynomial.X + Polynomial.C l)).coeff k =
      w ^ k *
        ∑ j ∈ Finset.range (n + 1), P.coeff j * ((Nat.fast_choose j k : ℚ) * l ^ (j - k)) := by
  unfold Polynomial.comp
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hP), Polynomial.finsetSum_coeff,
    Finset.mul_sum]
  simp only [Polynomial.coeff_C_mul, coeff_affine_pow, ← Nat.choose_eq_fast_choose]
  exact Finset.sum_congr rfl (fun _ _ ↦ by ring)

/-- Rational affine substitution gives the coefficients for a single real cell. -/
public theorem bernstein_rat_affine_eval (P : Polynomial ℚ) (n : ℕ) (hP : P.natDegree ≤ n) (l r : ℚ)
    (x : Set.Icc (0 : ℝ) 1) :
    P.eval₂ (Rat.castHom ℝ) (((r - l : ℚ) : ℝ) * x + (l : ℝ)) =
      ∑ j : Fin (n + 1),
        (bernsteinRatCoeff (P.comp (Polynomial.C (r - l) * Polynomial.X + Polynomial.C l)) n j :
            ℝ) *
          bernstein n j x := by
  let q := Polynomial.C (r - l) * Polynomial.X + Polynomial.C l
  have hq : q.natDegree ≤ 1 := by
    dsimp only [q]
    rw [Polynomial.natDegree_add_C]
    exact (Polynomial.natDegree_C_mul_le _ _).trans_eq Polynomial.natDegree_X
  have hdeg : (P.comp q).natDegree ≤ n :=
    (Polynomial.natDegree_comp_le.trans (Nat.mul_le_mul_left _ hq)).trans
      (by
        rw [mul_one]; exact hP)
  have h := bernstein_rat_coeff_eval (P.comp q) n hdeg x
  rw [Polynomial.eval₂_comp] at h
  simpa only [q, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X,
    Rat.coe_castHom] using h

/-- A weighted absolute integral of a rational polynomial reduces to a rational
sum of mean absolute Bernstein coefficients and exponential upper bounds. -/
public theorem weighted_abs_rat_bernstein (P : Polynomial ℚ) (N n : ℕ) (hP : P.natDegree ≤ n)
    {a : ℝ} (ha : 0 ≤ a) (p e : ℕ → ℚ) (hp : ∀ j < N, p j < p (j + 1))
    (he : ∀ j < N, Real.exp (-a * (p j : ℝ)) ≤ (e j : ℝ)) :
    (∫ x in (p 0 : ℝ)..(p N : ℝ), Real.exp (-a * x) * |P.eval₂ (Rat.castHom ℝ) x|) ≤
      ((∑ j ∈ Finset.range N,
          e j *
            ((p (j + 1) - p j) *
              ((∑ k : Fin (n + 1),
                  |bernsteinRatCoeff
                      (P.comp (Polynomial.C (p (j + 1) - p j) * Polynomial.X + Polynomial.C (p j)))
                      n k|) /
                ((n : ℚ) + 1)))) :
        ℚ) := by
  let c := fun (j : ℕ) (k : Fin (n + 1)) ↦
    bernsteinRatCoeff (P.comp (Polynomial.C (p (j + 1) - p j) * Polynomial.X + Polynomial.C (p j)))
      n k
  have hf : Continuous (fun x ↦ P.eval₂ (Rat.castHom ℝ) x) := Polynomial.continuous_eval₂ _ _
  have h :=
    weighted_abs_bernstein_partition _ hf ha N n (fun j ↦ (p j : ℝ)) (fun j k ↦ (c j k : ℝ))
      (fun j ↦ (e j : ℝ)) (fun j hj ↦ Rat.cast_lt.mpr (hp j hj)) he
      (fun j _ x ↦ by
        simpa only [Rat.cast_sub] using bernstein_rat_affine_eval P n hP (p j) (p (j + 1)) x)
  simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_sub, Rat.cast_div, Rat.cast_abs, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_one, c] using h

end PseudoPrime.Analysis
