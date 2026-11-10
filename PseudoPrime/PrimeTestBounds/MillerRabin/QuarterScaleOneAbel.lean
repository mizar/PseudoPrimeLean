/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterChebyshev
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularSupport
public import PseudoPrime.LLS.PaperStatements.TriangularJointCutoffBounds
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Variable-width scale-one Abel summation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a real width parameter and positive input, differentiate the
scale-one triangular upper-support weight `(2a - log t) t^(-1/2)`.
The product rule and the real-power addition law give the derivative used
in Abel summation of the variable-width principal series. -/
theorem quarter_scale_one_weight_deriv {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (2 * a - Real.log z) * z ^ (-1 / 2 : ℝ))
      (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) t := by
  have hd :=
    ((Real.hasDerivAt_log ht.ne').const_sub (2 * a)).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl ht.ne'))
  have hp := Real.rpow_add ht (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply hd.congr_deriv
  norm_num only
  rw [hp]
  ring

/-- On a positive compact interval, Abel summation expresses the variable
width scale-one weighted Mangoldt sum as two Chebyshev boundary terms minus
the integral of the explicit derivative against `ψ`. Differentiability and
integrability are established on the interval; this identity supplies the
unconditional high-index principal-cost estimate. -/
theorem quarter_scale_one_mangoldt_abel {a u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        ((2 * a - Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k =
      ((2 * a - Real.log v) * v ^ (-1 / 2 : ℝ)) * Chebyshev.psi v -
        ((2 * a - Real.log u) * u ^ (-1 / 2 : ℝ)) * Chebyshev.psi u -
        ∫ t in Set.Ioc u v, (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (2 * a - Real.log t) * t ^ (-1 / 2 : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc u v) :=
    quarter_scale_one_weight_deriv (a := a) (lt_of_lt_of_le hu ht.1)
  have he :
    Set.EqOn (deriv f) (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) (Set.Icc u v) :=
    fun t ht ↦ (hd t ht).deriv
  have hc :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) (Set.Icc u v) := by
    intro t ht
    have hp := lt_of_lt_of_le hu ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((Real.continuousAt_log hp.ne').div_const 2).sub_const a |>.sub_const
            1)).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc u v) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt hu.le huv
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- At a positive natural index within the support endpoint, the real
level-one triangular summand equals the variable-width Mangoldt weight.
The explicit transform and square-root power identity supply the termwise
bridge from the Mellin series to the Abel sum. -/
theorem quarter_scale_one_term {a X : ℝ} (ha : 0 < a) (hbound : Real.log X ≤ 2 * a) {n : ℕ}
    (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ X) :
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1 n).re =
      ((2 * a - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog0 := Real.log_nonneg hn1
  have hlog := Real.log_le_log hnpos hnX
  have hprof : LLS.PaperStatements.triangularKernelProfile a n = 2 * a - Real.log n := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [abs_of_nonneg hlog0, max_eq_right (by linarith only [hlog, hbound])]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0, div_one,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LLS.PaperStatements.triangular_transform_of_function _ ha rfl hnpos, hprof, neg_div,
    Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow]
  ring

/-- At the triangular support endpoint, the real scale-one principal series
is the negative Abel integral of the weight derivative against `ψ`. The
support identity reduces the series to a finite sum, the term at one
vanishes, and both Chebyshev boundary terms are zero. -/
theorem quarter_scale_one_series_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
            n).re =
      -∫ t in Set.Ioc 1 X, (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) * Chebyshev.psi t := by
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hzero :
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1 1).re =
      0 := by
    rw [quarter_scale_one_term ha hbound.le (by decide : 1 ≤ 1)
        (by simpa only [Nat.cast_one] using hX)]
    norm_num only [ArithmeticFunction.vonMangoldt_apply_one, mul_zero]
  have hfinite :
    (∑ k ∈ Finset.Icc 1 ⌊X⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
            k).re) =
      ∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊X⌋₊,
        ((2 * a - Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k := by
    rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons, hzero, zero_add]
    simp only [Nat.floor_one]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_Ioc.mp hk
    have hkX : (k : ℝ) ≤ X := (Nat.cast_le.mpr hk'.2).trans (Nat.floor_le (by linarith only [hX]))
    exact quarter_scale_one_term ha hbound.le hk'.1.le hkX
  have hsum :=
    congrArg Complex.re
      (quarter_triangular_scale_one_sum ha hX hbound.ge (1 : DirichletCharacter ℂ 1))
  simp only [Complex.re_sum] at hsum
  rw [hfinite] at hsum
  have habel := quarter_scale_one_mangoldt_abel (a := a) (u := 1) (v := X) (by norm_num only) hX
  rw [hbound] at habel
  simp only [sub_self, zero_mul, Chebyshev.psi_one, mul_zero, zero_sub] at habel
  exact hsum.trans habel

/-- On positive inputs, the product of the variable-width scale-one
variation weight and `t` has the displayed elementary primitive. The general
power-log derivative and the real-power addition law yield the identity;
it evaluates the main integral after applying the Chebyshev bound. -/
theorem quarter_scale_one_main_deriv {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 2 : ℝ) * (2 * a + 4 - Real.log z))
      (t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) * t) t := by
  have h :=
    LLS.PaperStatements.jointPowerLog_deriv (t := t) (r := 1 / 2) (a := 2 * a + 4) (b := -1) ht
  have hp := Real.rpow_add ht (-3 / 2) 1
  norm_num only [Real.rpow_one, neg_div] at hp
  convert h using 1
  · funext z
    ring
  · norm_num only [neg_div]
    rw [hp]
    ring

/-- The variable-width scale-one variation integral over `[1, X]` has an
explicit endpoint expression for `X ≥ 1`. The derivative identity and
continuity on the positive interval evaluate the Abel main term. -/
theorem quarter_scale_one_main_integral {a X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) * t) =
      X ^ (1 / 2 : ℝ) * (2 * a + 4 - Real.log X) - (2 * a + 4) := by
  have hc :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) * t) (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      (((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
              (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).mul
          continuousAt_id).continuousWithinAt
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        quarter_scale_one_main_deriv (a := a)
          (by
            rw [Set.uIcc_of_le hX] at ht; exact zero_lt_one.trans_le ht.1))
      hc.intervalIntegrable
  simpa only [Real.one_rpow, Real.log_one, sub_zero, one_mul] using h

/-- On the scale-one support interval, the nonnegative variation weight times
`ψ(t)` is at most three times the same weight times `t`. The support endpoint
makes the weight nonnegative, and the unconditional Chebyshev estimate supplies
the pointwise comparison needed for the principal-cost integral. -/
theorem quarter_scale_one_integrand_le {a X t : ℝ} (hbound : Real.log X = 2 * a) (ht : 1 ≤ t)
    (htX : t ≤ X) :
    (t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2)) * Chebyshev.psi t ≤
      3 * (t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) * t) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hlog := Real.log_le_log ht0 htX
  have hd : 0 ≤ t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) :=
    mul_nonneg (Real.rpow_nonneg ht0.le _) (by linarith only [hlog, hbound])
  have hψ := quarter_psi_le_three ht
  have hmul := mul_le_mul_of_nonneg_left hψ hd
  nlinarith only [hmul]

/-- On a triangular support interval `[1, X]`, integrate the pointwise
Chebyshev comparison for the variable-width scale-one variation weight.
Continuity and the finite Mangoldt representation establish integrability,
and interval integral monotonicity gives the upper main-term integral. -/
theorem quarter_scale_one_integral_le {a X : ℝ} (hX : 1 ≤ X) (hbound : Real.log X = 2 * a) :
    (∫ t in (1 : ℝ)..X, (t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2)) * Chebyshev.psi t) ≤
      3 * (∫ t in (1 : ℝ)..X, t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2) * t) := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2)
  have hd : ContinuousOn d (Set.Icc 1 X) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (fun t ↦ d t * Chebyshev.psi t) (Set.Ioc 1 X) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0)
        (by norm_num only : (0 : ℝ) ≤ 1) hd.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hdi : IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume 1 X :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr hi
  have hmi : IntervalIntegrable (fun t ↦ d t * t) MeasureTheory.volume 1 X :=
    (hd.mul continuousOn_id).intervalIntegrable_of_Icc hX
  have hb :=
    intervalIntegral.integral_mono_on hX hdi (hmi.const_mul 3)
      (fun t ht ↦ quarter_scale_one_integrand_le hbound ht.1 ht.2)
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb

/-- At its support endpoint, the scale-one principal series is at most twelve
times the square root of the endpoint. Abel summation and the unconditional
Chebyshev bound reduce the estimate to an explicit elementary integral. -/
theorem quarter_scale_one_principal_le {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
            n).re ≤
      12 * Real.sqrt X := by
  have habel := quarter_scale_one_series_abel ha hX hbound
  have heq :
    (fun t : ℝ ↦ (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - a - 1)) * Chebyshev.psi t) = fun t ↦
      -((t ^ (-3 / 2 : ℝ) * (a + 1 - Real.log t / 2)) * Chebyshev.psi t) := by
    funext t
    ring
  rw [heq, MeasureTheory.integral_neg, neg_neg, ← intervalIntegral.integral_of_le hX] at habel
  have hle := quarter_scale_one_integral_le hX hbound
  have hmain := quarter_scale_one_main_integral (a := a) hX
  rw [hbound, ← Real.sqrt_eq_rpow] at hmain
  nlinarith only [habel, hle, hmain, ha]

/-- Differentiate the increasing-log branch of the forward triangular weight
on positive inputs. The explicit derivative is used in Abel summation below
the forward scale. -/
theorem quarter_forward_weight_deriv {b t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (b + Real.log z) * z ^ (-1 / 2 : ℝ))
      (t ^ (-3 / 2 : ℝ) * (1 - (b + Real.log t) / 2)) t := by
  have hd :=
    ((Real.hasDerivAt_log ht.ne').const_add b).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl ht.ne'))
  have hp := Real.rpow_add ht (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply hd.congr_deriv
  norm_num only
  rw [hp]
  ring

/-- Abel summation for the increasing-log branch of a triangular principal
weight on a positive interval. The identity retains both Chebyshev boundary
terms and the exact derivative integral for the forward-scale estimate. -/
theorem quarter_forward_mangoldt_abel {b u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    ∑ k ∈ Finset.Ioc ⌊u⌋₊ ⌊v⌋₊,
        ((b + Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k =
      ((b + Real.log v) * v ^ (-1 / 2 : ℝ)) * Chebyshev.psi v -
        ((b + Real.log u) * u ^ (-1 / 2 : ℝ)) * Chebyshev.psi u -
        ∫ t in Set.Ioc u v, (t ^ (-3 / 2 : ℝ) * (1 - (b + Real.log t) / 2)) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (b + Real.log t) * t ^ (-1 / 2 : ℝ)
  have hd (t : ℝ) (ht : t ∈ Set.Icc u v) :=
    quarter_forward_weight_deriv (b := b) (lt_of_lt_of_le hu ht.1)
  have he :
    Set.EqOn (deriv f) (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (1 - (b + Real.log t) / 2)) (Set.Icc u v) :=
    fun t ht ↦ (hd t ht).deriv
  have hc :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (1 - (b + Real.log t) / 2)) (Set.Icc u v) := by
    intro t ht
    have hp := lt_of_lt_of_le hu ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (continuousAt_const.sub
            ((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const
              2))).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc u v) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt hu.le huv
      (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- At the forward scale equal to the support endpoint, a positive index
below that scale has logarithmic triangular weight. The transform formula
identifies the principal summand with the corresponding Mangoldt term. -/
theorem quarter_forward_term {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X = 2 * a)
    {n : ℕ} (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ X) :
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X n).re =
      (Real.log n * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hlog0 := Real.log_nonneg hn1
  have hlog := Real.log_le_log hnpos hnX
  have hprof : LLS.PaperStatements.triangularKernelProfile a ((n : ℝ) / X) = Real.log n := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [Real.log_div hnpos.ne' hXp.ne', abs_of_nonpos (by linarith only [hlog])]
    rw [max_eq_right (by linarith only [hlog0, hbound])]
    linarith only [hbound]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LLS.PaperStatements.triangular_transform_of_function _ ha rfl (div_pos hnpos hXp), hprof,
    neg_div, Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow]
  ring

/-- At the forward support endpoint, the finite principal sum below the scale
is the Abel expression for the logarithmic Mangoldt weight. This supplies the
lower-scale component of the full forward principal estimate. -/
theorem quarter_forward_finite_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re) =
      (Real.log X * X ^ (-1 / 2 : ℝ)) * Chebyshev.psi X -
        ∫ t in Set.Ioc 1 X, (t ^ (-3 / 2 : ℝ) * (1 - Real.log t / 2)) * Chebyshev.psi t := by
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons]
  have hzero :=
    quarter_forward_term ha hX hbound (by decide : 1 ≤ 1) (by simpa only [Nat.cast_one] using hX)
  norm_num only [Nat.cast_one, Real.log_one, zero_mul, mul_zero] at hzero
  rw [hzero, zero_add]
  have hfinite :
    (∑ n ∈ Finset.Ioc 1 ⌊X⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re) =
      ∑ n ∈ Finset.Ioc 1 ⌊X⌋₊,
        (Real.log n * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith only [hX]))
    exact quarter_forward_term ha hX hbound hn'.1.le hnX
  rw [hfinite]
  have h := quarter_forward_mangoldt_abel (b := 0) (u := 1) (v := X) (by norm_num only) hX
  simpa only [Nat.floor_one, zero_add, Real.log_one, zero_mul, Chebyshev.psi_one, mul_zero,
    sub_zero] using h

/-- Above the forward scale and below its support endpoint, the triangular
principal term is a decreasing logarithmic Mangoldt weight. This is the tail
branch of the full forward principal sum. -/
theorem quarter_forward_tail_term {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X) (hbound : Real.log X = 2 * a)
    {n : ℕ} (hXn : X ≤ n) (hnX : (n : ℝ) ≤ X ^ 2) :
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X n).re =
      ((4 * a - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le hXp hXn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hnpos)
  have hloglo := Real.log_le_log hXp hXn
  have hloghi := Real.log_le_log hnpos hnX
  rw [Real.log_pow] at hloghi
  norm_num only [Nat.cast_ofNat] at hloghi
  have hprof :
    LLS.PaperStatements.triangularKernelProfile a ((n : ℝ) / X) = 4 * a - Real.log n := by
    unfold LLS.PaperStatements.triangularKernelProfile
    rw [Real.log_div hnpos.ne' hXp.ne', abs_of_nonneg (by linarith only [hloglo])]
    rw [max_eq_right (by linarith only [hloghi, hbound])]
    linarith only [hbound]
  simp only [LLS.PaperStatements.MellinKernel.summand, ite_eq_right hn0,
    MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), mul_one, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [LLS.PaperStatements.triangular_transform_of_function _ ha rfl (div_pos hnpos hXp), hprof,
    neg_div, Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow]
  ring

/-- The portion of the forward principal sum between the scale and its
squared support endpoint is an exact Abel expression. The upper boundary
vanishes and the lower boundary is retained for cancellation. -/
theorem quarter_forward_tail_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X ^ 2⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re) =
      -((2 * a * X ^ (-1 / 2 : ℝ)) * Chebyshev.psi X) -
        ∫ t in Set.Ioc X (X ^ 2),
          (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 2 * a - 1)) * Chebyshev.psi t := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ X ^ 2 := by nlinarith only [hX, sq_nonneg (X - 1)]
  have hfinite :
    (∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X ^ 2⌋₊,
        ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re) =
      ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X ^ 2⌋₊,
        ((4 * a - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hXn : X ≤ (n : ℝ) := ((Nat.floor_lt hXp.le).mp hn'.1).le
    have hnX : (n : ℝ) ≤ X ^ 2 := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (sq_nonneg X))
    exact quarter_forward_tail_term ha hX hbound hXn hnX
  rw [hfinite]
  have h := quarter_scale_one_mangoldt_abel (a := 2 * a) (u := X) (v := X ^ 2) hXp hXX
  rw [Real.log_pow, hbound] at h
  norm_num only [Nat.cast_ofNat] at h
  convert h using 1 <;> ring_nf

/-- At the forward support endpoint, the full principal series equals the
sum of its two Abel integrals. The boundary terms at the forward scale cancel,
leaving the exact expression needed for the principal-cost upper bound. -/
theorem quarter_forward_series_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re =
      -(∫ t in Set.Ioc 1 X, (t ^ (-3 / 2 : ℝ) * (1 - Real.log t / 2)) * Chebyshev.psi t) -
        ∫ t in Set.Ioc X (X ^ 2),
          (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 2 * a - 1)) * Chebyshev.psi t := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ X ^ 2 := by nlinarith only [hX, sq_nonneg (X - 1)]
  have hY : 1 ≤ X ^ 2 := hX.trans hXX
  have hratio : 2 * a ≤ Real.log (X ^ 2 / X) := by
    rw [Real.log_div (pow_ne_zero 2 hXp.ne') hXp.ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [hbound]
  have hsum :=
    congrArg Complex.re
      (quarter_triangular_forward_sum ha hXp hY hratio (1 : DirichletCharacter ℂ 1))
  simp only [Complex.re_sum] at hsum
  let f := fun n : ℕ ↦
    ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X n).re
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hfloor2 : ⌊X⌋₊ ≤ ⌊X ^ 2⌋₊ := Nat.floor_mono hXX
  have hsplit :
    (∑ n ∈ Finset.Icc 1 ⌊X ^ 2⌋₊, f n) =
      (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, f n) + ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X ^ 2⌋₊, f n := by
    rw [Finset.Icc_eq_cons_Ioc (hfloor.trans hfloor2), Finset.sum_cons,
      Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons]
    rw [← Finset.sum_Ioc_consecutive f hfloor hfloor2]
    ring
  change _ = ∑ n ∈ Finset.Icc 1 ⌊X ^ 2⌋₊, f n at hsum
  rw [hsplit, quarter_forward_finite_abel ha hX hbound,
    quarter_forward_tail_abel ha hX hbound] at hsum
  rw [hbound] at hsum
  linarith only [hsum]

/-- A continuous nonnegative weight on an interval above one may be
integrated against `ψ` using the unconditional bound `ψ(t) ≤ 3t`. This
general comparison supplies both branches of the forward principal estimate. -/
theorem quarter_integral_psi_le {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) {d : ℝ → ℝ}
    (hd : ContinuousOn d (Set.Icc u v)) (hd0 : ∀ t ∈ Set.Icc u v, 0 ≤ d t) :
    (∫ t in u..v, d t * Chebyshev.psi t) ≤ 3 * ∫ t in u..v, d t * t := by
  have hi : MeasureTheory.IntegrableOn (fun t ↦ d t * Chebyshev.psi t) (Set.Ioc u v) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (by linarith only [hu])
        hd.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hdi : IntervalIntegrable (fun t ↦ d t * Chebyshev.psi t) MeasureTheory.volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr hi
  have hmi : IntervalIntegrable (fun t ↦ d t * t) MeasureTheory.volume u v :=
    (hd.mul continuousOn_id).intervalIntegrable_of_Icc huv
  have hb :=
    intervalIntegral.integral_mono_on huv hdi (hmi.const_mul 3)
      (fun t ht ↦ by
        have hp := quarter_psi_le_three (hu.trans ht.1)
        have hm := mul_le_mul_of_nonneg_left hp (hd0 t ht)
        nlinarith only [hm])
  rw [intervalIntegral.integral_const_mul] at hb
  exact hb

/-- The positive tail variation of the forward principal weight is bounded
by its explicit Chebyshev main integral on `[X, X²]`. The support endpoint
ensures nonnegativity and the elementary primitive evaluates the result. -/
theorem quarter_forward_tail_integral_le {a X : ℝ} (hX : 1 ≤ X) (hbound : Real.log X = 2 * a) :
    (∫ t in X..(X ^ 2), (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t) ≤
      3 * (4 * X - Real.sqrt X * (2 * a + 4)) := by
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXX : X ≤ X ^ 2 := by nlinarith only [hX, sq_nonneg (X - 1)]
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)
  have hd : ContinuousOn d (Set.Icc X (X ^ 2)) := by
    intro t ht
    have hp : 0 < t := hXp.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (continuousAt_const.sub ((Real.continuousAt_log hp.ne').div_const 2))).continuousWithinAt
  have hd0 : ∀ t ∈ Set.Icc X (X ^ 2), 0 ≤ d t := by
    intro t ht
    have hp : 0 < t := hXp.trans_le ht.1
    have hl := Real.log_le_log hp ht.2
    rw [Real.log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    exact mul_nonneg (Real.rpow_nonneg hp.le _) (by linarith only [hl, hbound])
  have hle := quarter_integral_psi_le hX hXX hd hd0
  have hc : ContinuousOn (fun t : ℝ ↦ d t * t) (Set.uIcc X (X ^ 2)) := by
    rw [Set.uIcc_of_le hXX]
    exact hd.mul continuousOn_id
  have hmain :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        quarter_scale_one_main_deriv (a := 2 * a)
          (by
            rw [Set.uIcc_of_le hXX] at ht; exact hXp.trans_le ht.1))
      hc.intervalIntegrable
  rw [Real.log_pow, hbound, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq_eq_abs,
    abs_of_nonneg hXp.le] at hmain
  norm_num only [Nat.cast_ofNat] at hmain
  simp only [d, neg_div] at hle ⊢
  rw [hmain] at hle
  convert hle using 1
  ring_nf

/-- The full forward principal series is bounded by its lower-scale Abel
integral plus an explicit upper-tail cost. The two support branches are
combined before applying the unconditional tail estimate. -/
theorem quarter_forward_principal_tail_le {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re ≤
      -(∫ t in Set.Ioc 1 X, (t ^ (-3 / 2 : ℝ) * (1 - Real.log t / 2)) * Chebyshev.psi t) +
        3 * (4 * X - Real.sqrt X * (2 * a + 4)) := by
  have hseries := quarter_forward_series_abel ha hX hbound
  have htail := quarter_forward_tail_integral_le hX hbound
  have hXX : X ≤ X ^ 2 := by nlinarith only [hX, sq_nonneg (X - 1)]
  rw [intervalIntegral.integral_of_le hXX] at htail
  have heq :
    (fun t : ℝ ↦ (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 2 * a - 1)) * Chebyshev.psi t) = fun t ↦
      -((t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t) := by
    funext t
    ring
  rw [heq, MeasureTheory.integral_neg] at hseries
  linarith only [hseries, htail]

/-- On the lower forward interval, dropping the negative part of the Abel
weight and using `ψ(t) ≤ 3t` bounds the integral by its elementary logarithmic
main term. This estimate complements the explicit forward tail bound. -/
theorem quarter_forward_lower_integral_le {X : ℝ} (hX : 1 ≤ X) :
    (∫ t in (1 : ℝ)..X, (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 1)) * Chebyshev.psi t) ≤
      3 * (Real.sqrt X * (Real.log X - 2) + 2) := by
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2)
  let e := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 1)
  have hcont (c : ℝ) :
    ContinuousOn (fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - c)) (Set.Icc 1 X) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((Real.continuousAt_log hp.ne').div_const 2).sub_const c)).continuousWithinAt
  have hd : ContinuousOn d (Set.Icc 1 X) := by simpa only [sub_zero] using hcont 0
  have he : ContinuousOn e (Set.Icc 1 X) := hcont 1
  have hd0 : ∀ t ∈ Set.Icc 1 X, 0 ≤ d t := by
    intro t ht
    exact
      mul_nonneg (Real.rpow_nonneg (zero_lt_one.trans_le ht.1).le _)
        (div_nonneg (Real.log_nonneg ht.1) (by norm_num only))
  have hψ := quarter_integral_psi_le (by norm_num only : (1 : ℝ) ≤ 1) hX hd hd0
  have hi (f : ℝ → ℝ) (hf : ContinuousOn f (Set.Icc 1 X)) :
    IntervalIntegrable (fun t ↦ f t * Chebyshev.psi t) MeasureTheory.volume 1 X := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0)
        (by norm_num only : (0 : ℝ) ≤ 1) hf.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hcomp :=
    intervalIntegral.integral_mono_on hX (hi e he) (hi d hd)
      (fun t ht ↦ by
        have hp : 0 ≤ t ^ (-3 / 2 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans_le ht.1).le _
        have hψ0 := Chebyshev.psi_nonneg t
        dsimp only [d, e]
        nlinarith only [mul_nonneg hp hψ0])
  have hc : ContinuousOn (fun t : ℝ ↦ d t * t) (Set.uIcc 1 X) := by
    rw [Set.uIcc_of_le hX]
    exact hd.mul continuousOn_id
  have hder (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 2 : ℝ) * (Real.log z - 2)) (d t * t) t := by
    have h := LLS.PaperStatements.jointPowerLog_deriv (t := t) (r := 1 / 2) (a := -2) (b := 1) ht
    have hp := Real.rpow_add ht (-3 / 2) 1
    norm_num only [Real.rpow_one, neg_div] at hp
    convert h using 1
    · funext z
      ring
    · dsimp only [d]
      norm_num only [neg_div]
      rw [hp]
      ring
  have hmain :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht ↦
        hder t
          (by
            rw [Set.uIcc_of_le hX] at ht; exact zero_lt_one.trans_le ht.1))
      hc.intervalIntegrable
  simp only [Real.log_one, ← Real.sqrt_eq_rpow, Real.sqrt_one, one_mul] at hmain
  dsimp only [e] at hcomp
  rw [hmain] at hψ
  linarith only [hcomp, hψ]

/-- At the forward support endpoint, the full principal series is at most
`12X`. The two Abel branches are bounded by the unconditional Chebyshev
estimate; their logarithmic endpoint terms cancel. -/
theorem quarter_forward_principal_upper {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑' n : ℕ,
          (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
            n).re ≤
      12 * X := by
  have htail := quarter_forward_principal_tail_le ha hX hbound
  have hlo := quarter_forward_lower_integral_le hX
  rw [intervalIntegral.integral_of_le hX] at hlo
  have heq :
    (fun t : ℝ ↦ (t ^ (-3 / 2 : ℝ) * (1 - Real.log t / 2)) * Chebyshev.psi t) = fun t ↦
      -((t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 1)) * Chebyshev.psi t) := by
    funext t
    ring
  rw [heq, MeasureTheory.integral_neg, neg_neg] at htail
  have hsqrt : (1 : ℝ) ≤ Real.sqrt X := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hX
  rw [hbound] at hlo
  nlinarith only [htail, hlo, hsqrt]

/-- Combining the finite forward principal sum with twice the complete
scale-one sum produces a single decreasing logarithmic weight. The scale-one
support makes both sums finite, and their terms combine exactly. -/
theorem quarter_joint_principal_weight {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
              n).re) +
        2 *
          (∑' n : ℕ,
              (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
                n).re =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        ((4 * a - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt n := by
  have hsum :=
    congrArg Complex.re
      (quarter_triangular_scale_one_sum ha hX hbound.ge (1 : DirichletCharacter ℂ 1))
  simp only [Complex.re_sum] at hsum
  rw [hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hnX : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le (by linarith only [hX]))
  rw [quarter_forward_term ha hX hbound hn'.1 hnX, quarter_scale_one_term ha hbound.le hn'.1 hnX]
  ring

/-- The combined forward and scale-one principal sums have a single Abel
formula with a positive variation weight on the support interval. This form
preserves the cancellation needed for the quantitative RH lower bound. -/
theorem quarter_joint_principal_abel {a X : ℝ} (ha : 0 < a) (hX : 1 ≤ X)
    (hbound : Real.log X = 2 * a) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
          ((LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) X
              n).re) +
        2 *
          (∑' n : ℕ,
              (LLS.PaperStatements.triangularMellinKernel ha).summand (1 : DirichletCharacter ℂ 1) 1
                n).re =
      (2 * a * X ^ (-1 / 2 : ℝ)) * Chebyshev.psi X +
        ∫ t in Set.Ioc 1 X,
          (t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t := by
  rw [quarter_joint_principal_weight ha hX hbound]
  have hfloor : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons]
  simp only [Nat.cast_one, ArithmeticFunction.vonMangoldt_apply_one, mul_zero, zero_add]
  have h := quarter_scale_one_mangoldt_abel (a := 2 * a) (u := 1) (v := X) (by norm_num only) hX
  rw [hbound] at h
  simp only [Nat.floor_one, Chebyshev.psi_one, mul_zero, sub_zero] at h
  have heq :
    (fun t : ℝ ↦ (t ^ (-3 / 2 : ℝ) * (Real.log t / 2 - 2 * a - 1)) * Chebyshev.psi t) = fun t ↦
      -((t ^ (-3 / 2 : ℝ) * (2 * a + 1 - Real.log t / 2)) * Chebyshev.psi t) := by
    funext t
    ring
  rw [heq, MeasureTheory.integral_neg] at h
  convert h using 1 <;> ring_nf

end PseudoPrime.PrimeTestBounds.MillerRabin
