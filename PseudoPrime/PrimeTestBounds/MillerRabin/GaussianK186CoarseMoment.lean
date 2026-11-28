/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighNegativeMoment

/-! # Negative moments from left-shifted power coefficients -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a nonnegative interval the negative part is bounded by the sum of
the negative coefficients weighted by powers of the right endpoint. -/
theorem negative_eval_le_power_sum (P : Polynomial ℝ) {x w : ℝ} {N : ℕ} (hN : P.natDegree < N)
    (hx : 0 ≤ x) (hxw : x ≤ w) :
    max 0 (-P.eval x) ≤ ∑ i ∈ Finset.range N, max 0 (-P.coeff i) * w ^ i := by
  have hterm (i : ℕ) : -(P.coeff i * x ^ i) ≤ max 0 (-P.coeff i) * w ^ i := by
    rw [← neg_mul]
    exact
      mul_le_mul (le_max_right _ _) (pow_le_pow_left₀ hx hxw i) (pow_nonneg hx _) (le_max_left _ _)
  refine
    max_le (Finset.sum_nonneg fun i _ ↦ mul_nonneg (le_max_left _ _) (pow_nonneg (hx.trans hxw) i))
      ?_
  rw [Polynomial.eval_eq_sum_range' hN, ← Finset.sum_neg_distrib]
  exact Finset.sum_le_sum fun i _ ↦ hterm i

/-- A uniform bound on the shifted negative part yields a cell integral
bound using the exponential at the left endpoint. -/
theorem negative_moment_cell_le (P : Polynomial ℝ) {s l w C E : ℝ} (hs : 0 ≤ s) (hw : 0 ≤ w)
    (hE : Real.exp (-s * l) ≤ E) (hP : ∀ x ∈ Set.Icc (0 : ℝ) w, max 0 (-P.eval (l + x)) ≤ C) :
    (∫ t in l..l + w, Real.exp (-s * t) * max 0 (-P.eval t)) ≤ w * (E * C) := by
  have hl : l ≤ l + w := le_add_of_nonneg_right hw
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-s * t) * max 0 (-P.eval t)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_const.max P.continuous.neg)
  calc
    (∫ t in l..l + w, Real.exp (-s * t) * max 0 (-P.eval t)) ≤ ∫ _ in l..l + w, E * C := by
      apply
        intervalIntegral.integral_mono_on hl (hc.intervalIntegrable l (l + w))
          (continuous_const.intervalIntegrable l (l + w))
      intro t ht
      have he := (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left ht.1 (neg_nonpos.mpr hs))).trans hE
      have hp :=
        hP (t - l)
          ⟨sub_nonneg.mpr ht.1, sub_le_iff_le_add.mpr (by simpa only [add_comm] using ht.2)⟩
      rw [show l + (t - l) = t by ring] at hp
      exact mul_le_mul he hp (le_max_left _ _) ((Real.exp_nonneg _).trans hE)
    _ = _ := by rw [intervalIntegral.integral_const, add_sub_cancel_left, smul_eq_mul]

/-- The power-coefficient sum of the left translate supplies the uniform
negative-part bound required for a cell integral. -/
theorem negative_moment_le_shift_sum (P : Polynomial ℝ) {s l w E : ℝ} {N : ℕ} (hs : 0 ≤ s)
    (hw : 0 ≤ w) (hE : Real.exp (-s * l) ≤ E)
    (hN : (P.comp (Polynomial.X + Polynomial.C l)).natDegree < N) :
    let Q := P.comp (Polynomial.X + Polynomial.C l)
    (∫ t in l..l + w, Real.exp (-s * t) * max 0 (-P.eval t)) ≤
      w * (E * ∑ i ∈ Finset.range N, max 0 (-Q.coeff i) * w ^ i) := by
  intro Q
  refine negative_moment_cell_le P hs hw hE ?_
  intro x hx
  have h := negative_eval_le_power_sum Q hN hx.1 hx.2
  simpa only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    add_comm x l] using h

/-- The K186 negative-moment cell uses a fixed 84-entry coefficient range
at every derivative order. -/
public theorem k186_negative_moment_cell (j : ℕ) {l w E : ℝ} (hw : 0 ≤ w)
    (hE : Real.exp (-(9 / 4 : ℝ) * l) ≤ E) :
    let P := (Polynomial.derivative^[j]) HighGaussianKernel.k186.realProfile
    let Q := P.comp (Polynomial.X + Polynomial.C l)
    (∫ t in l..l + w, Real.exp (-(9 / 4 : ℝ) * t) * max 0 (-P.eval t)) ≤
      w * (E * ∑ i ∈ Finset.range 84, max 0 (-Q.coeff i) * w ^ i) := by
  have hd (k : ℕ) :
    ((Polynomial.derivative^[k]) HighGaussianKernel.k186.realProfile).natDegree ≤ 83 := by
    induction k with
    | zero =>
      rw [Function.iterate_zero, id_eq, ← high_comp_profile_map]
      exact Polynomial.natDegree_map_le.trans (high_rat_profile_degree .k186)
    | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact (Polynomial.natDegree_derivative_le _).trans ((Nat.sub_le _ _).trans hk)
  intro P Q
  have hQ : Q.natDegree ≤ 83 :=
    Polynomial.natDegree_comp_le.trans
      (by simpa only [Polynomial.natDegree_X_add_C, mul_one] using hd j)
  exact negative_moment_le_shift_sum P (by norm_num only) hw hE (Nat.lt_succ_of_le hQ)

/-- Left endpoint of each width-six cell of the K186 correction interval. -/
@[expose]
public noncomputable def k186MomentLeft (i : ℕ) : ℝ :=
  35 + 6 * i

/-- The five cell integrals cover the full correction interval. Any verified
cell caps can therefore be summed before applying the H30 formula. -/
public theorem k186_negative_moment_le_cells (j : ℕ) (C : ℕ → ℝ)
    (hC :
      ∀ i ∈ Finset.range 5,
        let P := (Polynomial.derivative^[j]) HighGaussianKernel.k186.realProfile
        (∫ t in k186MomentLeft i..k186MomentLeft i + 6,
            Real.exp (-(9 / 4 : ℝ) * t) * max 0 (-P.eval t)) ≤
          C i) :
    highNegativeMoment .k186 j ≤ ∑ i ∈ Finset.range 5, C i := by
  let P := (Polynomial.derivative^[j]) HighGaussianKernel.k186.realProfile
  let f := fun t : ℝ ↦ Real.exp (-(9 / 4 : ℝ) * t) * max 0 (-P.eval t)
  have hc : Continuous f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (continuous_const.max P.continuous.neg)
  have hi (i : ℕ) : k186MomentLeft (i + 1) = k186MomentLeft i + 6 := by
    simp only [k186MomentLeft, Nat.cast_add, Nat.cast_one]
    ring
  have hs :=
    intervalIntegral.sum_integral_adjacent_intervals (n := 5) (μ := MeasureTheory.volume) (a :=
      k186MomentLeft) (f := f)
      (fun i _ ↦ hc.intervalIntegrable (k186MomentLeft i) (k186MomentLeft (i + 1)))
  have he : highNegativeMoment .k186 j = ∫ t in k186MomentLeft 0..k186MomentLeft 5, f t := by
    norm_num only [highNegativeMoment, profileCorrectionStart, profileCorrectionEnd,
      HighGaussianKernel.pole, Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, f, P, k186MomentLeft,
      Nat.cast_zero, Nat.cast_ofNat]
  rw [he, ← hs]
  exact Finset.sum_le_sum fun i hi' ↦ by simpa only [hi, f, P] using hC i hi'

/-- Differentiating a left translate only rescales and shifts its coefficient
indices. The three moment checks can reuse the same translated input row. -/
public theorem shifted_derivative_coeff (P : Polynomial ℝ) (l : ℝ) (j i : ℕ) :
    (((Polynomial.derivative^[j]) P).comp (Polynomial.X + Polynomial.C l)).coeff i =
      ((i + j).descFactorial j : ℝ) * (P.comp (Polynomial.X + Polynomial.C l)).coeff (i + j) := by
  have h (k : ℕ) :
    ((Polynomial.derivative^[k]) P).comp (Polynomial.X + Polynomial.C l) =
      (Polynomial.derivative^[k]) (P.comp (Polynomial.X + Polynomial.C l)) := by
    induction k with
    | zero => rfl
    | succ k hk =>
      simp only [Function.iterate_succ_apply', ← hk, Polynomial.derivative_comp,
        Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
        one_mul]
  rw [h j, Polynomial.coeff_iterate_derivative, nsmul_eq_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
