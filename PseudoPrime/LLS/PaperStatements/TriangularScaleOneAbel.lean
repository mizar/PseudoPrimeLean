/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularPrincipalUpperBounds
public import PseudoPrime.LLS.RiemannChebyshevNumericalBounds

/-! # Finite scale-one triangular sum and Abel identity -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the triangular support, the finite scale-one principal sum equals the upper-weight
Mangoldt sum. The term at one vanishes, and the floor endpoint is retained. -/
theorem scaleOne_finite_eq_upper {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 36) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) 1 k).re) =
      (∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊,
        ((36 - Real.log ((k : ℝ) / 1)) * ((k : ℝ) / 1) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k) := by
  have hfloor : 1 ≤ ⌊x⌋₊ := by exact Nat.le_floor (by exact_mod_cast hx)
  have hzero :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand (1 : DirichletCharacter ℂ 1)
          1 1).re =
      0 := by
    rw [triangular18_level_one_term (x := 1) (by norm_num only) (by norm_num only)]
    norm_num only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul]
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons, hzero, zero_add]
  simp only [Nat.floor_one]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_Ioc.mp hk
  have hlow : (1 : ℝ) ≤ k := by exact_mod_cast hk'.1.le
  have hhigh : (k : ℝ) ≤ Real.exp 36 * 1 := by
    have h := (Nat.cast_le.mpr hk'.2).trans (Nat.floor_le (zero_lt_one.trans_le hx).le)
    simpa only [mul_one] using h.trans hu
  have ht := triangular18_level_one_upper_term (x := 1) (by norm_num only) hlow hhigh
  simpa only [Real.sqrt_one, div_one] using ht

/-- For a cutoff between one and the support endpoint, express the finite scale-one
principal sum using Chebyshev's function and an Abel integral. The lower boundary
vanishes because the Chebyshev function is zero at one. -/
theorem scaleOne_finite_abel {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 36) :
    (∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) 1 k).re) =
      (36 - Real.log x) * x ^ (-1 / 2 : ℝ) * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x, t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * Chebyshev.psi t := by
  rw [scaleOne_finite_eq_upper hx hu]
  have h :=
    Analysis.triangular18_upper_scaled_mangoldt_abel (x := 1) (a := 1) (b := x) (by norm_num only)
      (by norm_num only) hx
  simpa only [div_one, Chebyshev.psi_one, mul_zero, sub_zero] using h

/-- Evaluate the Abel main-term integral on an arbitrary interval beginning at one.
Use the explicit upper-weight primitive; this keeps the cutoff boundary visible. -/
theorem scaleOne_main_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * t) =
      x ^ (1 / 2 : ℝ) * (Real.log x - 40) + 40 := by
  have hc :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * t) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      (((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
              ((Real.continuousAt_log hp.ne').div_const 2 |>.sub continuousAt_const)).mul
          continuousAt_id).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        Analysis.triangular18_upper_main_deriv
          (by
            rw [Set.uIcc_of_le hx] at ht; exact zero_lt_one.trans_le ht.1))
      hc.intervalIntegrable
  simpa only [Real.one_rpow, Real.log_one, one_mul, zero_sub, sub_neg_eq_add] using h

/-- Evaluate the error-weight integral on an arbitrary interval beginning at one.
The variation primitive retains its lower boundary for the explicit Chebyshev error. -/
theorem scaleOne_error_integral {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in (1 : ℝ)..x, t ^ (-3 / 4 : ℝ) * (19 - Real.log t / 2)) =
      x ^ (1 / 4 : ℝ) * (84 - 2 * Real.log x) - 84 := by
  have hc : ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 4 : ℝ) * (19 - Real.log t / 2)) (Set.uIcc 1 x) := by
    rw [Set.uIcc_of_le hx]
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 4) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        Analysis.triangular18_upper_variation_deriv
          (by
            rw [Set.uIcc_of_le hx] at ht; exact zero_lt_one.trans_le ht.1))
      hc.intervalIntegrable
  simpa only [Real.one_rpow, Real.log_one, mul_zero, sub_zero, one_mul] using h

/-- Under RH on the triangular support, bound the Abel integrand above by its main
term and explicit positive error profile. The derivative is nonpositive, so the
one-sided Chebyshev lower bound gives the required direction. -/
theorem scaleOne_integrand_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 ≤ t)
    (hu : t ≤ Real.exp 36) :
    t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * Chebyshev.psi t ≤
      t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * t +
        13 * (t ^ (-3 / 4 : ℝ) * (19 - Real.log t / 2)) := by
  have hp : 0 < t := zero_lt_one.trans_le ht
  have hlog := Real.log_le_log hp hu
  rw [Real.log_exp] at hlog
  have hd : t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hp.le _) (by linarith only [hlog])
  have he := (abs_le.mp (LLS.psi_error_le_thirteen hRH hp.le)).1
  have hm := mul_le_mul_of_nonpos_left he hd
  have hr : t ^ (-3 / 2 : ℝ) * t ^ (3 / 4 : ℝ) = t ^ (-3 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  rw [← hr]
  nlinarith only [hm]

/-- Under RH, integrate the one-sided Chebyshev estimate over the triangular support.
The finite Mangoldt step function and both explicit profiles are integrable on the
compact interval; monotonicity bounds the Abel integral by its main and error terms. -/
theorem scaleOne_abel_integral_le (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hu : x ≤ Real.exp 36) :
    (∫ t in (1 : ℝ)..x, t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * Chebyshev.psi t) ≤
      (∫ t in (1 : ℝ)..x, t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19) * t) +
        13 * (∫ t in (1 : ℝ)..x, t ^ (-3 / 4 : ℝ) * (19 - Real.log t / 2)) := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 19)
  let e := fun t : ℝ ↦ t ^ (-3 / 4 : ℝ) * (19 - Real.log t / 2)
  have hd : ContinuousOn d (Set.Icc 1 x) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          ((Real.continuousAt_log hp.ne').div_const 2 |>.sub continuousAt_const)).continuousWithinAt
  have he : ContinuousOn e (Set.Icc 1 x) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 4) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (fun t ↦ d t * Chebyshev.psi t) (Set.Ioc 1 x) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0)
        (by norm_num only : (0 : ℝ) ≤ 1) hd.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hdi : IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume 1 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr hi
  have hmi : IntervalIntegrable (fun t ↦ d t * t) MeasureTheory.volume 1 x :=
    (hd.mul continuousOn_id).intervalIntegrable_of_Icc hx
  have hei : IntervalIntegrable e MeasureTheory.volume 1 x := he.intervalIntegrable_of_Icc hx
  have hri := hmi.add (hei.const_mul 13)
  have hb :=
    intervalIntegral.integral_mono_on hx hdi hri
      (fun t ht ↦ scaleOne_integrand_le hRH ht.1 (ht.2.trans hu))
  rw [intervalIntegral.integral_add hmi (hei.const_mul 13),
    intervalIntegral.integral_const_mul] at hb
  exact hb

/-- Under RH, the finite scale-one principal sum has the explicit lower bound on the
entire triangular support from one to exp 36. Combine Abel summation, the one-sided
Chebyshev error, and the exact main and error integrals including both boundary terms. -/
theorem scaleOne_finite_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hu : x ≤ Real.exp 36) :
    2 * Real.sqrt x * (38 - Real.log x) - (1560 - 39 * Real.log x) * x ^ (1 / 4 : ℝ) + 1052 ≤
      ∑ k ∈ Finset.Icc 1 ⌊x⌋₊,
        ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
            (1 : DirichletCharacter ℂ 1) 1 k).re := by
  have hp : 0 < x := zero_lt_one.trans_le hx
  have hl := Real.log_le_log hp hu
  rw [Real.log_exp] at hl
  have hw : 0 ≤ (36 - Real.log x) * x ^ (-1 / 2 : ℝ) :=
    mul_nonneg (by linarith only [hl]) (Real.rpow_nonneg hp.le _)
  have he := (abs_le.mp (LLS.psi_error_le_thirteen hRH hp.le)).1
  have he' : x - 13 * x ^ (3 / 4 : ℝ) ≤ Chebyshev.psi x := by linarith only [he]
  have hb := mul_le_mul_of_nonneg_left he' hw
  have hi := scaleOne_abel_integral_le hRH hx hu
  rw [scaleOne_main_integral hx, scaleOne_error_integral hx] at hi
  rw [← Real.sqrt_eq_rpow] at hi
  have hr : x ^ (-1 / 2 : ℝ) * x = Real.sqrt x := by
    have h := Real.rpow_add hp (-1 / 2) 1
    norm_num only [Real.rpow_one] at h
    simpa only [neg_div, Real.sqrt_eq_rpow] using h.symm
  have hs : x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ) = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_add hp]
    congr 1
    norm_num only
  have heq :
    (36 - Real.log x) * x ^ (-1 / 2 : ℝ) * (x - 13 * x ^ (3 / 4 : ℝ)) =
      (36 - Real.log x) * (Real.sqrt x - 13 * x ^ (1 / 4 : ℝ)) := by
    calc
      _ = (36 - Real.log x) * (x ^ (-1 / 2 : ℝ) * x - 13 * (x ^ (-1 / 2 : ℝ) * x ^ (3 / 4 : ℝ))) :=
        by ring
      _ = _ := by rw [hr, hs]
  rw [heq] at hb
  rw [scaleOne_finite_abel hx hu, ← intervalIntegral.integral_of_le hx]
  nlinarith only [hb, hi, hr, hs]

end PseudoPrime.LLS.PaperStatements
