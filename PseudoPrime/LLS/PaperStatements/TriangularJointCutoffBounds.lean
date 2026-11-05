/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularCreditedInterior
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneAbel

/-! # Joint scale and scale-one triangular cutoff -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On the inner triangular support, combine the finite level-one sums at scale x
and scale one into a single Mangoldt-weighted sum. The floor endpoint and both
kernel profiles are preserved, including the boundary at exp 36. -/
theorem triangular18_joint_weight {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 36) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n) * (108 - Real.log x - Real.log n) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hlogx : Real.log x ≤ 36 := by
    have hh := Real.log_le_log hxp hu
    simpa only [Real.log_exp] using hh
  dsimp only
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn'.1
  have hnp : 0 < (n : ℝ) := zero_lt_one.trans_le hn1
  have hn0 : n ≠ 0 := Nat.ne_of_gt (Nat.cast_pos.mp hnp)
  have hnx : (n : ℝ) ≤ x := (Nat.cast_le.mpr hn'.2).trans (Nat.floor_le hxp.le)
  have hln0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlnx := Real.log_le_log hnp hnx
  have hdiv : Real.log ((n : ℝ) / x) = Real.log n - Real.log x := Real.log_div hnp.ne' hxp.ne'
  have hprofilex : triangularKernelProfile 18 ((n : ℝ) / x) = 36 + Real.log n - Real.log x := by
    unfold triangularKernelProfile
    rw [hdiv, abs_of_nonpos (by linarith only [hlnx] : Real.log n - Real.log x ≤ 0)]
    norm_num only
    rw [max_eq_right (by linarith only [hln0, hlogx])]
    ring
  have hprofile1 : triangularKernelProfile 18 ((n : ℝ) / 1) = 36 - Real.log n := by
    rw [div_one]
    unfold triangularKernelProfile
    rw [abs_of_nonneg hln0]
    norm_num only
    exact max_eq_right (by linarith only [hlnx, hlogx])
  have htermx := triangular18_level_one_term (x := x) hxp hn0
  have hterm1 := triangular18_level_one_term (x := 1) (by norm_num only) hn0
  change (K.summand (1 : DirichletCharacter ℂ 1) x n).re = _ at htermx
  change (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re = _ at hterm1
  rw [htermx, hterm1, hprofilex, hprofile1]
  ring

/-- Differentiate the joint triangular weight on positive inputs. The logarithm of
the cutoff is a fixed parameter during Abel summation. -/
theorem triangular18_joint_weight_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ (108 - Real.log x - Real.log z) * z ^ (-1 / 2 : ℝ))
      (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)) t := by
  have h :=
    (((Real.hasDerivAt_log ht.ne').neg).const_add (108 - Real.log x)).mul
      (Real.hasDerivAt_rpow_const (p := -1 / 2) (Or.inl ht.ne'))
  have hp := Real.rpow_add ht (-1) (-1 / 2)
  norm_num only at hp
  rw [Real.rpow_neg_one] at hp
  apply h.congr_deriv
  norm_num only
  rw [neg_mul, ← hp]
  simp only [Pi.neg_apply]
  ring

/-- Apply Abel summation to the joint weight on a real cutoff at least one.
The finite interval uses floor endpoints, and the lower Chebyshev boundary vanishes. -/
theorem triangular18_joint_abel {x : ℝ} (hx : 1 ≤ x) :
    (∑ k ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊,
        ((108 - Real.log x - Real.log k) * (k : ℝ) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt k) =
      ((108 - Real.log x - Real.log x) * x ^ (-1 / 2 : ℝ)) * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x,
          (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)) * Chebyshev.psi t := by
  let f := fun t : ℝ ↦ (108 - Real.log x - Real.log t) * t ^ (-1 / 2 : ℝ)
  let d := fun t : ℝ ↦ t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) :=
    triangular18_joint_weight_deriv (x := x) (zero_lt_one.trans_le ht.1)
  have he : Set.EqOn (deriv f) d (Set.Icc 1 x) := fun t ht ↦ (hd t ht).deriv
  have hc : ContinuousOn d (Set.Icc 1 x) := by
    intro t ht
    have hp : 0 < t := zero_lt_one.trans_le ht.1
    exact
      ((Real.continuousAt_rpow_const t (-3 / 2) (Or.inl hp.ne')).mul
          (((continuousAt_const.add (Real.continuousAt_log hp.ne')).div_const 2).sub
            continuousAt_const)).continuousWithinAt
  have hi : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 1 x) := (hc.congr he).integrableOn_Icc
  have h :=
    sum_mul_eq_sub_sub_integral_mul ArithmeticFunction.vonMangoldt (by norm_num only : (0 : ℝ) ≤ 1)
      hx (fun t ht ↦ (hd t ht).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_one, mul_zero, sub_zero] at h
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ congrArg (fun z : ℝ ↦ z * Chebyshev.psi t) (he ⟨ht.1.le, ht.2⟩))] at h
  exact h

/-- On the inner support, express the combined principal sum by the joint Abel
integral and its endpoint. The summand at one vanishes and no integer endpoint is lost. -/
theorem triangular18_joint_sum_abel {x : ℝ} (hx : 1 ≤ x) (hu : x ≤ Real.exp 36) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
        2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) =
      ((108 - 2 * Real.log x) * x ^ (-1 / 2 : ℝ)) * Chebyshev.psi x -
        ∫ t in Set.Ioc 1 x,
          (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)) * Chebyshev.psi t := by
  dsimp only
  rw [triangular18_joint_weight hx hu]
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
  have hz :
    ArithmeticFunction.vonMangoldt 1 / Real.sqrt (1 : ℕ) * (108 - Real.log x - Real.log (1 : ℕ)) =
      0 := by
    norm_num only [ArithmeticFunction.vonMangoldt_apply_one, zero_div, zero_mul]
  rw [Finset.Icc_eq_cons_Ioc hfloor, Finset.sum_cons, hz, zero_add]
  have hsum :
    (∑ n ∈ Finset.Ioc 1 ⌊x⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (108 - Real.log x - Real.log n)) =
      ∑ n ∈ Finset.Ioc ⌊(1 : ℝ)⌋₊ ⌊x⌋₊,
        ((108 - Real.log x - Real.log n) * (n : ℝ) ^ (-1 / 2 : ℝ)) *
          ArithmeticFunction.vonMangoldt n := by
    simp only [Nat.floor_one]
    apply Finset.sum_congr rfl
    intro n hn
    have hnp : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [neg_div, Real.rpow_neg hnp, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    ring
  rw [hsum, triangular18_joint_abel hx]
  congr 2
  ring

/-- Differentiate a power times an affine logarithm at a positive input.
This identity supplies the three explicit primitives for the joint Abel estimate. -/
theorem jointPowerLog_deriv {t r a b : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ r * (a + b * Real.log z))
      (t ^ (r - 1) * (r * (a + b * Real.log t) + b)) t := by
  have h :=
    (Real.hasDerivAt_rpow_const (p := r) (Or.inl ht.ne')).mul
      (((Real.hasDerivAt_log ht.ne').const_mul b).const_add a)
  have hp : t ^ r = t ^ (r - 1) * t := by
    have e := Real.rpow_add ht (r - 1) 1
    simp only [sub_add_cancel, Real.rpow_one] at e
    exact e
  have htinv : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have he : t ^ (r - 1) * t * (b * t⁻¹) = t ^ (r - 1) * b := by
    calc
      _ = t ^ (r - 1) * b * (t * t⁻¹) := by ring
      _ = _ := by rw [htinv, mul_one]
  apply h.congr_deriv
  rw [hp, he]
  ring

/-- The main term of the joint Abel integral has an explicit positive-scale primitive. -/
theorem joint_main_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 2 : ℝ) * (112 - Real.log x - Real.log z))
      (t ^ (-1 / 2 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) t := by
  have h := jointPowerLog_deriv (t := t) (r := 1 / 2) (a := 112 - Real.log x) (b := -1) ht
  convert h using 1
  all_goals
    first
    | (funext z; ring)
    | (norm_num only; ring)

/-- The three-quarter error term has an explicit positive-scale primitive. -/
theorem joint_threeQuarter_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ (1 / 4 : ℝ) * (228 - 2 * Real.log x - 2 * Real.log z))
      (t ^ (-3 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) t := by
  have h := jointPowerLog_deriv (t := t) (r := 1 / 4) (a := 228 - 2 * Real.log x) (b := -2) ht
  convert h using 1
  all_goals
    first
    | (funext z; ring)
    | (norm_num only; ring)

/-- The quarter-power error term has an explicit positive-scale primitive. -/
theorem joint_quarter_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun z : ℝ ↦ z ^ (-1 / 4 : ℝ) * (-212 + 2 * Real.log x + 2 * Real.log z))
      (t ^ (-5 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) t := by
  have h := jointPowerLog_deriv (t := t) (r := -1 / 4) (a := -212 + 2 * Real.log x) (b := 2) ht
  convert h using 1
  norm_num only
  ring

/-- An explicit primitive for the joint Chebyshev lower-bound integrand.
The cutoff logarithm is fixed while the integration variable ranges over positive reals. -/
noncomputable def triangular18_jointPrimitive (x t : ℝ) : ℝ :=
  t ^ (1 / 2 : ℝ) * (112 - Real.log x - Real.log t) -
      (19 / 30 : ℝ) * (t ^ (1 / 4 : ℝ) * (228 - 2 * Real.log x - 2 * Real.log t)) -
      (63 / 10 : ℝ) * (t ^ (-1 / 4 : ℝ) * (-212 + 2 * Real.log x + 2 * Real.log t)) +
    (1839 / 1000 : ℝ) * ((108 - Real.log x - Real.log t) * t ^ (-1 / 2 : ℝ))

/-- Differentiate the joint primitive term by term. Its main, two power-error,
and constant-error components retain their boundary contributions. -/
theorem triangular18_jointPrimitive_deriv {x t : ℝ} (ht : 0 < t) :
    HasDerivAt (triangular18_jointPrimitive x)
      (t ^ (-1 / 2 : ℝ) * ((110 - Real.log x - Real.log t) / 2) -
          (19 / 30 : ℝ) * (t ^ (-3 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) -
          (63 / 10 : ℝ) * (t ^ (-5 / 4 : ℝ) * ((110 - Real.log x - Real.log t) / 2)) +
        (1839 / 1000 : ℝ) * (t ^ (-3 / 2 : ℝ) * ((Real.log x + Real.log t) / 2 - 55)))
      t := by
  have hm := joint_main_deriv (x := x) ht
  have h3 := joint_threeQuarter_deriv (x := x) ht
  have h1 := joint_quarter_deriv (x := x) ht
  have hw := triangular18_joint_weight_deriv (x := x) ht
  have h :=
    ((hm.sub (h3.const_mul (19 / 30))).sub (h1.const_mul (63 / 10))).add
      (hw.const_mul (1839 / 1000))
  exact h

end PseudoPrime.LLS.PaperStatements
