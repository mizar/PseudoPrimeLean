/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

/-! # Curvature of logarithmic polynomial terms in the K131 bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the product of a real power and a polynomial in twice the logarithm. -/
@[expose]
noncomputable def logPowerPoly (e : ℝ) (P : Polynomial ℝ) (y : ℝ) : ℝ :=
  y ^ e * P.eval (2 * Real.log y)

private noncomputable def logPowerDiff (e : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C e * P + Polynomial.C 2 * P.derivative

/-- The polynomial giving the normalized second derivative of a term
whose real-power exponent is minus p. -/
@[expose]
noncomputable def logPowerCurvature (p : ℝ) (P : Polynomial ℝ) : Polynomial ℝ :=
  Polynomial.C (p * (p + 1)) * P - Polynomial.C (2 * (2 * p + 1)) * P.derivative +
    Polynomial.C 4 * P.derivative.derivative

private theorem log_power_poly_deriv (e : ℝ) (P : Polynomial ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (logPowerPoly e P) (logPowerPoly (e - 1) (logPowerDiff e P) y) y := by
  have hl := (Real.hasDerivAt_log hy.ne').const_mul 2
  have hP := (P.hasDerivAt (2 * Real.log y)).comp y hl
  have hR := Real.hasDerivAt_rpow_const (p := e) (Or.inl hy.ne')
  convert hR.mul hP using 1
  · rfl
  · simp only [logPowerPoly, logPowerDiff, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Function.comp_def]
    rw [Real.rpow_sub_one hy.ne']
    ring

private theorem log_power_curvature_eval (p : ℝ) (P : Polynomial ℝ) (x : ℝ) :
    (logPowerDiff (-p - 1) (logPowerDiff (-p) P)).eval x = (logPowerCurvature p P).eval x := by
  simp only [logPowerDiff, logPowerCurvature, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_C, zero_mul, zero_add, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C]
  ring

/-- The derivative of the first derivative of a K131 power term is
the curvature polynomial evaluated at twice the logarithm and scaled
by the power with exponent lowered by two. -/
theorem log_power_poly_second (p : ℝ) (P : Polynomial ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (deriv (logPowerPoly (-p) P)) (logPowerPoly (-p - 2) (logPowerCurvature p P) y)
      y := by
  have h := log_power_poly_deriv (-p - 1) (logPowerDiff (-p) P) hy
  have he : ((-p - 1) - 1 : ℝ) = -p - 2 := by ring
  rw [he] at h
  apply (h.congr_deriv ?_).congr_of_eventuallyEq
  · filter_upwards [isOpen_Ioi.mem_nhds hy] with t ht
    exact (log_power_poly_deriv (-p) P ht).deriv
  · unfold logPowerPoly
    rw [log_power_curvature_eval]

/-- Multiplication by the square of the radius cancels the two extra inverse
powers in the second derivative, as in the K131 concavity certificate. -/
theorem log_power_poly_curvature (p : ℝ) (P : Polynomial ℝ) {y : ℝ} (hy : 0 < y) :
    y ^ 2 * deriv (deriv (logPowerPoly (-p) P)) y =
      logPowerPoly (-p) (logPowerCurvature p P) y := by
  rw [(log_power_poly_second p P hy).deriv]
  unfold logPowerPoly
  rw [Real.rpow_sub hy, Real.rpow_ofNat]
  field_simp [hy.ne']

/-- A finite sum of logarithmic power terms, plus a twice differentiable
remainder, is concave when its normalized curvature sum is nonpositive.
This is the sign condition checked on the K131 bridge. -/
theorem log_power_sum_concave {ι : Type*} (s : Finset ι) (p : ι → ℝ) (P : ι → Polynomial ℝ)
    {a b : ℝ} (ha : 0 < a) {R R' R'' : ℝ → ℝ} (hR : ∀ y ∈ Set.Icc a b, HasDerivAt R (R' y) y)
    (hR' : ∀ y ∈ Set.Ioo a b, HasDerivAt R' (R'' y) y)
    (hcurv :
      ∀ y ∈ Set.Ioo a b,
        (∑ i ∈ s, logPowerPoly (-p i) (logPowerCurvature (p i) (P i)) y) + y ^ 2 * R'' y ≤ 0) :
    ConcaveOn ℝ (Set.Icc a b) (fun y ↦ (∑ i ∈ s, logPowerPoly (-p i) (P i) y) + R y) := by
  let f := fun y ↦ (∑ i ∈ s, logPowerPoly (-p i) (P i) y) + R y
  let d := fun y ↦ (∑ i ∈ s, deriv (logPowerPoly (-p i) (P i)) y) + R' y
  let dd := fun y ↦ (∑ i ∈ s, logPowerPoly (-p i - 2) (logPowerCurvature (p i) (P i)) y) + R'' y
  have hd (y : ℝ) (hy : y ∈ Set.Icc a b) : HasDerivAt f (d y) y := by
    have hpos := ha.trans_le hy.1
    have hi (i : ι) :
      HasDerivAt (logPowerPoly (-p i) (P i)) (deriv (logPowerPoly (-p i) (P i)) y) y := by
      have h := log_power_poly_deriv (-p i) (P i) hpos
      rw [h.deriv]
      exact h
    exact (HasDerivAt.fun_sum (fun i _ ↦ hi i)).add (hR y hy)
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := d) (f'' := dd) (convex_Icc a b)
  · exact fun y hy ↦ (hd y hy).continuousAt.continuousWithinAt
  · exact fun y hy ↦ (hd y (interior_subset hy)).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    exact
      ((HasDerivAt.fun_sum (fun i _ ↦ log_power_poly_second (p i) (P i) (ha.trans hy.1))).add
          (hR' y hy)).hasDerivWithinAt
  · intro y hy
    rw [interior_Icc] at hy
    have hpos := ha.trans hy.1
    apply nonpos_of_mul_nonpos_right _ (sq_pos_of_pos hpos)
    dsimp only [dd]
    rw [mul_add, Finset.mul_sum]
    have he (i : ι) :
      y ^ 2 * logPowerPoly (-p i - 2) (logPowerCurvature (p i) (P i)) y =
        logPowerPoly (-p i) (logPowerCurvature (p i) (P i)) y := by
      rw [← (log_power_poly_second (p i) (P i) hpos).deriv]
      exact log_power_poly_curvature (p i) (P i) hpos
    simp only [he]
    exact hcurv y hy

end PseudoPrime.PrimeTestBounds.MillerRabin
