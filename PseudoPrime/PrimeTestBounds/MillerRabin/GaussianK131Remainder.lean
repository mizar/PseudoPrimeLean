/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Exponential
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Tactic

/-! # Curvature of the principal RH error in the K131 comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The signed contribution of the principal RH error, with positive
coefficient c and doubled logarithmic coordinate. -/
@[expose]
noncomputable def k131PrincipalError (c y : ℝ) : ℝ :=
  let l := 2 * Real.log y
  (-c) * (l * (l - Real.log l))

private noncomputable def principalSlope (c y : ℝ) : ℝ :=
  let l := 2 * Real.log y
  (-c) * (2 * l - Real.log l - 1) * (2 / y)

private theorem principal_error_deriv (c : ℝ) {y : ℝ} (hy : 1 < y) :
    HasDerivAt (k131PrincipalError c) (principalSlope c y) y := by
  have yp := zero_lt_one.trans hy
  have hl := (Real.hasDerivAt_log yp.ne').const_mul 2
  have hp : 0 < 2 * Real.log y := mul_pos (by norm_num only) (Real.log_pos hy)
  have h := (hl.mul (hl.sub (hl.log hp.ne'))).const_mul (-c)
  convert h using 1
  · rfl
  · simp only [principalSlope, Pi.sub_apply]
    field_simp [yp.ne', (Real.log_pos hy).ne']
    ring

private theorem principal_slope_deriv (c : ℝ) {y : ℝ} (hy : 1 < y) :
    let l := 2 * Real.log y
    HasDerivAt (principalSlope c) (c * (4 * l - 10 + 4 / l - 2 * Real.log l) / y ^ 2) y := by
  intro l
  have yp := zero_lt_one.trans hy
  have hl := (Real.hasDerivAt_log yp.ne').const_mul 2
  have hp : 0 < 2 * Real.log y := mul_pos (by norm_num only) (Real.log_pos hy)
  have hA := (((hl.const_mul 2).sub (hl.log hp.ne')).sub_const 1).const_mul (-c)
  have hB := (hasDerivAt_const y (2 : ℝ)).div (hasDerivAt_id y) yp.ne'
  convert hA.mul hB using 1
  · rfl
  · simp only [id_eq, l, Pi.sub_apply, Pi.div_apply]
    field_simp [yp.ne', (Real.log_pos hy).ne']
    ring

/-- After multiplying by the radius squared, the curvature of the signed
RH error is a scalar expression in twice the logarithm. -/
theorem k131_principal_curvature (c : ℝ) {y : ℝ} (hy : 1 < y) :
    let l := 2 * Real.log y
    y ^ 2 * deriv (deriv (k131PrincipalError c)) y = c * (4 * l - 10 + 4 / l - 2 * Real.log l) := by
  intro l
  have h := principal_slope_deriv c hy
  dsimp only at h
  have hd :
    HasDerivAt (deriv (k131PrincipalError c)) (c * (4 * l - 10 + 4 / l - 2 * Real.log l) / y ^ 2)
      y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (principal_error_deriv c ht).deriv
  rw [hd.deriv, mul_div_cancel₀ _ (sq_pos_of_pos (zero_lt_one.trans hy)).ne']

/-- On the logarithmic domain [14,17], the normalized curvature of the
principal RH error is bounded by 4/5 if its coefficient is at most 7/480. -/
theorem k131_principal_curvature_le {c y : ℝ} (hc : c ∈ Set.Icc 0 (7 / 480)) (hy : 1 < y)
    (hl : 2 * Real.log y ∈ Set.Icc (14 : ℝ) 17) :
    y ^ 2 * deriv (deriv (k131PrincipalError c)) y ≤ 4 / 5 := by
  have hlog : 2 ≤ Real.log (2 * Real.log y) := by
    have h8 : Real.log (8 : ℝ) ≤ Real.log (2 * Real.log y) :=
      Real.log_le_log (by norm_num only) (by linarith only [hl.1])
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow] at h8
    norm_num only [Nat.cast_ofNat] at h8
    linarith only [h8, Real.log_two_gt_d9]
  have hdiv :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 4) (by norm_num only : (0 : ℝ) < 14)
      hl.1
  have h := k131_principal_curvature c hy
  dsimp only at h
  rw [h]
  have hcap :
    4 * (2 * Real.log y) - 10 + 4 / (2 * Real.log y) - 2 * Real.log (2 * Real.log y) ≤ 380 / 7 := by
    linarith only [hdiv, hl.2, hlog]
  exact
    (mul_le_mul_of_nonneg_left hcap hc.1).trans
      ((mul_le_mul_of_nonneg_right hc.2 (by norm_num only : (0 : ℝ) ≤ 380 / 7)).trans
        (by norm_num only))

/-- The negative inverse-square-root term from finite square recovery
has nonpositive normalized curvature at every positive radius. -/
theorem k131_recovery_curvature_le {D y : ℝ} (hD : 0 ≤ D) (hy : 0 < y) :
    y ^ 2 * deriv (deriv (logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D)))) y ≤ 0 := by
  rw [log_power_poly_curvature (1 / 2) (Polynomial.C (-D)) hy]
  simp only [logPowerPoly, logPowerCurvature, Polynomial.derivative_C, Polynomial.derivative_zero,
    mul_zero, sub_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
  exact
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hy.le _)
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num only) (neg_nonpos.mpr hD))

/-- The K131 expanded comparison is concave once the polynomial part has
normalized curvature at most minus 43/50. The principal error costs at most
4/5 and the finite square recovery has nonpositive curvature. -/
theorem k131_comparison_concave {ι : Type*} (s : Finset ι) (p : ι → ℝ) (P : ι → Polynomial ℝ)
    {a b c D : ℝ} (ha : 1 < a) (hc : c ∈ Set.Icc 0 (7 / 480)) (hD : 0 ≤ D)
    (hlog : ∀ y ∈ Set.Icc a b, 2 * Real.log y ∈ Set.Icc (14 : ℝ) 17)
    (hpoly :
      ∀ y ∈ Set.Ioo a b,
        (∑ i ∈ s, logPowerPoly (-p i) (logPowerCurvature (p i) (P i)) y) ≤ -43 / 50) :
    ConcaveOn ℝ (Set.Icc a b)
      (fun y ↦
        (∑ i ∈ s, logPowerPoly (-p i) (P i) y) +
          (k131PrincipalError c y + logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D)) y)) := by
  let f := k131PrincipalError c
  let g := logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D))
  apply
    log_power_sum_concave s p P (zero_lt_one.trans ha) (R := fun y ↦ f y + g y) (R' := fun y ↦
      deriv f y + deriv g y) (R'' := fun y ↦ deriv (deriv f) y + deriv (deriv g) y)
  · intro y hy
    have hp := ha.trans_le hy.1
    have hf := principal_error_deriv c hp
    have hg := Real.hasDerivAt_rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (zero_lt_one.trans hp).ne')
    have hg' : HasDerivAt g (-(1 / 2 : ℝ) * y ^ (-(1 / 2 : ℝ) - 1) * (-D)) y := by
      convert hg.mul_const (-D) using 1
      funext t
      simp only [g, logPowerPoly, Polynomial.eval_C]
    rw [hf.deriv, hg'.deriv]
    exact hf.add hg'
  · intro y hy
    have hp := ha.trans hy.1
    have hf := principal_slope_deriv c hp
    have hf' :
      HasDerivAt (deriv f)
        (c * (4 * (2 * Real.log y) - 10 + 4 / (2 * Real.log y) - 2 * Real.log (2 * Real.log y)) /
          y ^ 2)
        y := by
      apply hf.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioi.mem_nhds hp] with t ht
      exact (principal_error_deriv c ht).deriv
    have hg := log_power_poly_second (1 / 2) (Polynomial.C (-D)) (zero_lt_one.trans hp)
    rw [hf'.deriv, hg.deriv]
    exact hf'.add hg
  · intro y hy
    have hp := ha.trans hy.1
    have hc' := k131_principal_curvature_le hc hp (hlog y ⟨hy.1.le, hy.2.le⟩)
    have hd := k131_recovery_curvature_le hD (zero_lt_one.trans hp)
    dsimp only [f, g]
    rw [mul_add]
    linarith only [hpoly y hy, hc', hd]

/-- For a reciprocal term with coefficient at most 81, the normalized
curvature contributes at most 7/50 throughout the K131 radius interval. -/
theorem k131_reciprocal_curvature_le {A y : ℝ} (hA : A ≤ 81) (hy : (465644807 / 400000 : ℝ) ≤ y) :
    logPowerPoly (-1 : ℝ) (logPowerCurvature 1 (Polynomial.C A)) y ≤ 7 / 50 := by
  have hp : 0 < y := (by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le hy
  simp only [logPowerPoly, logPowerCurvature, Polynomial.derivative_C, Polynomial.derivative_zero,
    mul_zero, sub_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Real.rpow_neg_one, inv_mul_eq_div]
  apply (div_le_iff₀ hp).mpr
  linarith only [hA, hy]

/-- The normalized polynomial curvature and two scalar endpoint checks
certify the K131 gap throughout the affine bridge. -/
theorem k131_gap_of_poly_bounds {ι : Type*} (s : Finset ι) (p : ι → ℝ) (P : ι → Polynomial ℝ)
    {c D L : ℝ} (hc : c ∈ Set.Icc 0 (7 / 480)) (hD : 0 ≤ D) (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a : ℝ := 465644807 / 400000
    let b : ℝ := 1036273 / 250
    let G := fun y ↦
      (∑ i ∈ s, logPowerPoly (-p i) (P i) y) +
        (k131PrincipalError c y + logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D)) y)
    (∀ y ∈ Set.Ioo a b,
        (∑ i ∈ s, logPowerPoly (-p i) (logPowerCurvature (p i) (P i)) y) ≤ -43 / 50) →
      1 / 200 < G a → 1 / 200 < G b → 1 / 200 < G (gaussianBridgeScale L) := by
  intro a b G hpoly hleft hright
  apply gaussian_bridge_gap_pos hL _ hleft hright
  apply k131_comparison_concave s p P (by norm_num only [a] : 1 < a) hc hD _ hpoly
  intro y hy
  let U := (y + 123 / 10) / (519674 / 1000000 : ℝ)
  have hU : U ∈ Set.Icc (9055 / 4 : ℝ) 8000 := by
    dsimp only [U]
    exact
      ⟨by linarith only [show (465644807 / 400000 : ℝ) ≤ y from hy.1], by
        linarith only [show y ≤ (1036273 / 250 : ℝ) from hy.2]⟩
  have h := k131_radius_log_mem hU
  have he : gaussianBridgeScale U = y := by
    dsimp only [gaussianBridgeScale, U]; ring
  rwa [he] at h

end PseudoPrime.PrimeTestBounds.MillerRabin
