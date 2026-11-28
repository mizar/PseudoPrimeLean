/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Reflection
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Reflection
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Polynomials
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Tactic

/-! # Curvature of the higher K131 reflection moments -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private structure SlopeCap (P : Polynomial ℝ) (x c : ℝ) : Prop where
  value_nonneg : 0 ≤ P.eval x
  slope_nonneg : 0 ≤ P.derivative.eval x
  second_nonneg : 0 ≤ P.derivative.derivative.eval x
  slope_le : P.derivative.eval x ≤ c * P.eval x

private theorem SlopeCap.mul {P Q : Polynomial ℝ} {x c d : ℝ} (hP : SlopeCap P x c)
    (hQ : SlopeCap Q x d) : SlopeCap (P * Q) x (c + d) := by
  have h₁ := mul_le_mul_of_nonneg_right hP.slope_le hQ.value_nonneg
  have h₂ := mul_le_mul_of_nonneg_left hQ.slope_le hP.value_nonneg
  constructor
  · rw [Polynomial.eval_mul]
    exact mul_nonneg hP.value_nonneg hQ.value_nonneg
  · rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul]
    positivity [hP.value_nonneg, hQ.value_nonneg, hP.slope_nonneg, hQ.slope_nonneg]
  · simp only [Polynomial.derivative_mul, Polynomial.derivative_add, Polynomial.eval_add,
      Polynomial.eval_mul]
    positivity [hP.value_nonneg, hQ.value_nonneg, hP.slope_nonneg, hQ.slope_nonneg,
      hP.second_nonneg, hQ.second_nonneg]
  · simp only [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul]
    nlinarith only [h₁, h₂]

private theorem SlopeCap.pow {P : Polynomial ℝ} {x c : ℝ} (hP : SlopeCap P x c) (n : ℕ) :
    SlopeCap (P ^ n) x ((n : ℝ) * c) := by
  induction n with
  | zero =>
    simp only [pow_zero, Nat.cast_zero, zero_mul]
    exact
      ⟨by norm_num only [Polynomial.eval_one], by
        simp only [Polynomial.derivative_one, Polynomial.eval_zero, le_refl], by
        simp only [Polynomial.derivative_one, Polynomial.derivative_zero, Polynomial.eval_zero,
          le_refl],
        by simp only [Polynomial.derivative_one, Polynomial.eval_zero, zero_mul, le_refl]⟩
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, add_mul, one_mul]
    exact ih.mul hP

private theorem SlopeCap.affine (a b x c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ a * x + b)
    (hc : a ≤ c * (a * x + b)) : SlopeCap (Polynomial.C a * Polynomial.X + Polynomial.C b) x c := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  · simpa only [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, mul_one, add_zero, Polynomial.eval_C] using ha
  · simp only [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, mul_one, add_zero, Polynomial.eval_zero, le_refl]
  · simpa only [Polynomial.derivative_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
      Polynomial.derivative_C, mul_one, add_zero, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using hc

private theorem SlopeCap.curvature {P : Polynomial ℝ} {x c : ℝ} (hP : SlopeCap P x c)
    (hc : 29 * c ≤ 837 / 16) : 0 ≤ (logPowerCurvature (27 / 4) P).eval x := by
  have h := mul_le_mul_of_nonneg_right hc hP.value_nonneg
  have h' := mul_le_mul_of_nonneg_left hP.slope_le (by norm_num only : (0 : ℝ) ≤ 29)
  simp only [logPowerCurvature, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C]
  linarith only [h, h', hP.second_nonneg]

private theorem reflect_affine_cap {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) :
    SlopeCap (Polynomial.C 2 * Polynomial.X - Polynomial.C h) x (20 / 237) := by
  rw [sub_eq_add_neg, ← Polynomial.C_neg]
  apply SlopeCap.affine
  · norm_num only
  · linarith only [hx, hh]
  · linarith only [hx, hh]

private theorem physical_log_cap {x : ℝ} (hx : 141 / 10 ≤ x) :
    SlopeCap Polynomial.X x (10 / 141) := by
  have h :=
    SlopeCap.affine 1 0 x (10 / 141) (by norm_num only) (by linarith only [hx])
      (by linarith only [hx])
  simpa only [Polynomial.C_1, one_mul, Polynomial.C_0, add_zero] using h

private theorem reflect_gamma_cap {x h m : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) (hm : m ≤ 19) :
    SlopeCap
      (Polynomial.C (35 / 16) * (Polynomial.C 2 * Polynomial.X - Polynomial.C h) - Polynomial.C m) x
      (67 / 500) := by
  have he :
    Polynomial.C (35 / 16 : ℝ) * (Polynomial.C 2 * Polynomial.X - Polynomial.C h) - Polynomial.C m =
      Polynomial.C (35 / 8) * Polynomial.X + Polynomial.C (-(35 / 16 : ℝ) * h - m) := by
    rw [mul_sub, ← mul_assoc, ← Polynomial.C_mul, ← Polynomial.C_mul, sub_sub, ← Polynomial.C_add,
      sub_eq_add_neg, ← Polynomial.C_neg]
    have h₁ : (35 / 16 : ℝ) * 2 = 35 / 8 := by norm_num only
    have h₂ : -((35 / 16 : ℝ) * h + m) = -(35 / 16 : ℝ) * h - m := by ring
    rw [h₁, h₂]
  rw [he]
  apply SlopeCap.affine
  · norm_num only
  · linarith only [hx, hh, hm]
  · linarith only [hx, hh, hm]

/-- Every shifted monomial in the higher reflection term has nonnegative
curvature. The two unshifted logarithmic powers are covered together. -/
theorem k131_higher_monomial_curvature {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) {j k : ℕ}
    (hj : j ≤ 19) (hk : k ≤ 2) :
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k * (Polynomial.C 2 * Polynomial.X - Polynomial.C h) ^ j)).eval
        x := by
  have hj' : (j : ℝ) ≤ 19 := by exact_mod_cast hj
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  exact
    (((physical_log_cap hx).pow k).mul ((reflect_affine_cap hx hh).pow j)).curvature
      (by linarith only [hj', hk'])

/-- The differentiated Gamma monomial in the higher reflection term has
nonnegative curvature. The degree and the coefficient of its linear
correction are both bounded by the K131 inverse Mellin degree. -/
theorem k131_higher_gamma_curvature {x h m : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) (hm : m ≤ 19)
    {j k : ℕ} (hj : j ≤ 18) (hk : k ≤ 2) :
    let S : Polynomial ℝ := Polynomial.C 2 * Polynomial.X - Polynomial.C h
    0 ≤
      (logPowerCurvature (27 / 4)
            ((Polynomial.X ^ k * S ^ j) * (Polynomial.C (35 / 16) * S - Polynomial.C m))).eval
        x := by
  intro S
  have hj' : (j : ℝ) ≤ 18 := by exact_mod_cast hj
  have hk' : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  exact
    ((((physical_log_cap hx).pow k).mul ((reflect_affine_cap hx hh).pow j)).mul
          (reflect_gamma_cap hx hh hm)).curvature
      (by linarith only [hj', hk'])

private theorem curvature_add (p x : ℝ) (P Q : Polynomial ℝ) :
    (logPowerCurvature p (P + Q)).eval x =
      (logPowerCurvature p P).eval x + (logPowerCurvature p Q).eval x := by
  simp only [logPowerCurvature, Polynomial.derivative_add, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C]
  ring

private theorem gamma_monomial_comp {h : ℝ} {n : ℕ} (hn : 0 < n) :
    let S : Polynomial ℝ := Polynomial.C 2 * Polynomial.X - Polynomial.C h
    (gammaMainPoly (Polynomial.X ^ n)).comp S =
      S ^ (n - 1) * (Polynomial.C (35 / 16) * S - Polynomial.C (n : ℝ)) := by
  intro S
  rw [gammaMainPoly, Polynomial.sub_comp, Polynomial.derivative_X_pow, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp, Polynomial.mul_comp,
    Polynomial.C_comp, Polynomial.pow_comp, Polynomial.X_comp]
  have hp : S ^ n = S ^ (n - 1) * S := by
    conv_lhs => rw [← Nat.sub_add_cancel (Nat.one_le_of_lt hn), pow_add, pow_one]
  rw [hp]
  ring

private theorem gamma_atom_curvature {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) {n k : ℕ}
    (hn : n ≤ 19) (hk : k ≤ 2) :
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k *
              (gammaMainPoly (Polynomial.X ^ n)).comp
                (Polynomial.C 2 * Polynomial.X - Polynomial.C h))).eval
        x := by
  let S : Polynomial ℝ := Polynomial.C 2 * Polynomial.X - Polynomial.C h
  change
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k * (gammaMainPoly (Polynomial.X ^ n)).comp S)).eval
        x
  by_cases h : n = 0
  · subst n
    simp only [pow_zero, gammaMainPoly, Polynomial.derivative_one, mul_one, sub_zero,
      Polynomial.C_comp, mul_comm (Polynomial.X ^ k), curvature_scale]
    apply mul_nonneg (by norm_num only)
    have h0 := k131_higher_monomial_curvature hx hh (j := 0) (by decide) hk
    simpa only [pow_zero, mul_one] using h0
  · rw [gamma_monomial_comp (Nat.pos_of_ne_zero h), ← mul_assoc]
    have hm : (n : ℝ) ≤ 19 := by exact_mod_cast hn
    have hj : n - 1 ≤ 18 := Nat.sub_le_sub_right hn 1
    exact k131_higher_gamma_curvature hx hh hm hj hk

private theorem higher_gamma_of_poly {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2)
    (P : Polynomial ℝ) (hP : P.natDegree ≤ 19) (hC : ∀ n, 0 ≤ P.coeff n) {k : ℕ} (hk : k ≤ 2) :
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k *
              (gammaMainPoly P).comp (Polynomial.C 2 * Polynomial.X - Polynomial.C h))).eval
        x := by
  have hrep :
    gammaMainPoly P =
      ∑ n ∈ P.support, Polynomial.C (P.coeff n) * gammaMainPoly (Polynomial.X ^ n) := by
    unfold gammaMainPoly
    conv_lhs => rw [P.as_sum_support_C_mul_X_pow]
    simp only [Finset.mul_sum, Polynomial.derivative_sum, Polynomial.derivative_C_mul,
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [hrep, Polynomial.sum_comp, Finset.mul_sum, curvature_sum]
  apply Finset.sum_nonneg
  intro n hn
  rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_assoc, mul_comm (Polynomial.X ^ k), mul_assoc,
    curvature_scale]
  exact
    mul_nonneg (hC n)
      (gamma_atom_curvature hx hh
        ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)).trans hP) hk)

private theorem higher_moment_curvature {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) {k : ℕ}
    (hk : k ≤ 2) (m : ℕ) :
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k *
              (k131MomentPoly (gammaMainPoly gaussianK131InversePoly) (27 / 16) m).comp
                (Polynomial.C 2 * Polynomial.X - Polynomial.C h))).eval
        x := by
  unfold k131MomentPoly
  rw [Polynomial.sum_comp, Finset.mul_sum, curvature_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_assoc, mul_comm (Polynomial.X ^ k), mul_assoc,
    curvature_scale]
  apply mul_nonneg (by positivity)
  have he :
    (Polynomial.derivative^[j]) (gammaMainPoly gaussianK131InversePoly) =
      gammaMainPoly ((Polynomial.derivative^[j]) gaussianK131InversePoly) := by
    simp only [gammaMainPoly, Polynomial.iterate_derivative_sub,
      Polynomial.iterate_derivative_C_mul]
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply']
  rw [he]
  apply higher_gamma_of_poly hx hh _ _ _ hk
  · exact
      (Polynomial.natDegree_iterate_derivative _ _).trans ((Nat.sub_le _ _).trans inverse_degree_le)
  · intro n
    rw [Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
    exact mul_nonneg (Nat.cast_nonneg _) (inverse_coeff_nonneg _)

private theorem higher_inverse_curvature {x h : ℝ} (hx : 141 / 10 ≤ x) (hh : h ≤ 9 / 2) {k : ℕ}
    (hk : k ≤ 2) :
    0 ≤
      (logPowerCurvature (27 / 4)
            (Polynomial.X ^ k *
              gaussianK131InversePoly.comp (Polynomial.C 2 * Polynomial.X - Polynomial.C h))).eval
        x := by
  rw [gaussianK131InversePoly, Polynomial.sum_comp, Finset.mul_sum, curvature_sum]
  apply Finset.sum_nonneg
  intro j _
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.mul_comp, Polynomial.C_comp,
    Polynomial.pow_comp, Polynomial.X_comp, ← mul_assoc, mul_comm (Polynomial.X ^ k), mul_assoc,
    curvature_scale]
  have hC : 0 ≤ inverseCoeffs j := (show ∀ i : Fin 9, 0 ≤ inverseCoeffs i by decide +kernel) j
  exact
    mul_nonneg (Rat.cast_nonneg.mpr hC)
      (k131_higher_monomial_curvature hx hh
        (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ j.isLt)) 3) hk)

/-- The normalized curvature of the higher reflection polynomial is
nonpositive throughout the actual K131 radius interval. -/
theorem gaussian_k131_poly_higher_curvature {y : ℝ} (hy : 0 < y)
    (hlog : 141 / 10 ≤ 2 * Real.log y) :
    logPowerPoly (-(27 / 4 : ℝ)) (logPowerCurvature (27 / 4) gaussianK131PolyHigher) y ≤ 0 := by
  unfold logPowerPoly gaussianK131PolyHigher
  apply mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hy.le _)
  rw [curvature_sum]
  apply Finset.sum_nonpos
  intro j _
  rw [curvature_scale]
  apply
    mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (reflect_factor_nonpos j) (by norm_num only))
  have hh := reflection_offset_le j
  have hB := higher_inverse_curvature hlog hh (k := 2) (by decide)
  have h₀ := higher_moment_curvature hlog hh (k := 2) (by decide) 0
  have h₁ := higher_moment_curvature hlog hh (k := 1) (by decide) 1
  have h₂ := higher_moment_curvature hlog hh (k := 0) (by decide) 2
  dsimp only [reflectPoly]
  rw [mul_add, curvature_add, curvature_add, curvature_add, mul_assoc, curvature_scale]
  simp only [pow_one, pow_zero, one_mul] at h₁ h₂
  exact add_nonneg (add_nonneg (add_nonneg hB h₀) (mul_nonneg (by norm_num only) h₁)) h₂

/-- Both reflection signs now follow from the actual inverse Mellin
polynomial. Positivity of the K131 comparison needs only the remaining
two polynomial signs and the two endpoint checks. -/
theorem gaussian_k131_gap_of_main_signs {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000)
    (hsign :
      ∀ y ∈ Set.Ioo (465644807 / 400000 : ℝ) (1036273 / 250),
        logPowerPoly (-(19 / 8 : ℝ)) (logPowerCurvature (19 / 8) gaussianK131Poly19) y ≤ -1 ∧
          logPowerPoly (-(27 / 8 : ℝ)) (logPowerCurvature (27 / 8) gaussianK131Poly27) y ≤ 0)
    (hleft : 1 / 200 < gaussianK131Gap (465644807 / 400000))
    (hright : 1 / 200 < gaussianK131Gap (1036273 / 250)) :
    1 / 200 < gaussianK131Gap (gaussianBridgeScale L) := by
  apply gaussian_k131_gap_of_signs hL _ hleft hright
  intro y hy
  have hpos : (0 : ℝ) < 465644807 / 400000 := by norm_num only
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 465644807 / 400000) (j := 10) (n := 12) (lo :=
        141 / 20) (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo
  have hlog : 141 / 10 ≤ 2 * Real.log y := by linarith only [hlo, Real.log_le_log hpos hy.1.le]
  exact ⟨(hsign y hy).1, (hsign y hy).2, gaussian_k131_poly_higher_curvature (hpos.trans hy.1) hlog⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
