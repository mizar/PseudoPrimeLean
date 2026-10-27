/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.MeanInequalities
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
public import Mathlib.Tactic

/-! # Explicit finite exponential Mangoldt bounds from Chebyshev error

Abel summation and a common affine envelope for t^(3/4) yield a finite lower bound.
Keeping the boundary and integral errors together avoids losing a factor of two.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The finite exponentially weighted Mangoldt sum at scale x and cutoff y.
The natural floor selects n≤y; the zero index contributes zero. Positive x gives
the smoothing sum used by the shifted Gamma Mellin kernel. -/
noncomputable def exponentialMangoldtSum (x y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n

/-- For every real scale and nonnegative cutoff, exponential smoothing equals
the psi boundary term plus its weighted integral. Apply Abel summation and differentiate
the exponential weight. This is the exact finite interface for quantitative error bounds. -/
theorem exponentialMangoldtSum_eq_psi_integral (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    exponentialMangoldtSum x y =
      Real.exp (-y / x) * Chebyshev.psi y +
        (1 / x) * ∫ t in Set.Ioc 0 y, Real.exp (-t / x) * Chebyshev.psi t := by
  unfold exponentialMangoldtSum
  have hd (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ Real.exp (-u / x)) (-(1 / x) * Real.exp (-t / x)) t := by
    have h := ((hasDerivAt_id t).neg.div_const x).exp
    change HasDerivAt (fun u : ℝ ↦ Real.exp (-u / x)) (Real.exp (-t / x) * (-1 / x)) t at h
    exact h.congr_deriv (by ring)
  have hf : Continuous (fun t : ℝ ↦ -(1 / x) * Real.exp (-t / x)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_id.neg.div_const x))
  have hdEq : deriv (fun t : ℝ ↦ Real.exp (-t / x)) = fun t ↦ -(1 / x) * Real.exp (-t / x) :=
    funext (fun t ↦ (hd t).deriv)
  have hi : MeasureTheory.IntegrableOn (deriv (fun t : ℝ ↦ Real.exp (-t / x))) (Set.Icc 0 y) := by
    rw [hdEq]
    exact hf.integrableOn_Icc
  have h :=
    sum_mul_eq_sub_integral_mul ArithmeticFunction.vonMangoldt hy
      (fun t _ ↦ (hd t).differentiableAt) hi
  simp only [← Chebyshev.psi_eq_sum_Icc, (hd _).deriv] at h
  have he :
    (∫ t in Set.Ioc 0 y, (-(1 / x) * Real.exp (-t / x)) * Chebyshev.psi t) =
      -(1 / x) * ∫ t in Set.Ioc 0 y, Real.exp (-t / x) * Chebyshev.psi t := by
    simp only [mul_assoc, MeasureTheory.integral_const_mul]
  rw [he] at h
  linarith only [h]

/-- For t≥0 and x>0, t^(3/4) is bounded by the tangent affine expression
x^(3/4)(1/4+3t/(4x)). Weighted AM-GM at t/x proves the inequality.
It bounds the boundary and integral Chebyshev errors by the same envelope. -/
private theorem three_quarter_rpow_le_scaled_affine {t x : ℝ} (ht : 0 ≤ t) (hx : 0 < x) :
    t ^ (3 / 4 : ℝ) ≤ x ^ (3 / 4 : ℝ) * (1 / 4 + 3 / 4 * (t / x)) := by
  have h :=
    Real.geom_mean_le_arith_mean2_weighted (by norm_num only : (0 : ℝ) ≤ 1 / 4)
      (by norm_num only : (0 : ℝ) ≤ 3 / 4) (by norm_num only : (0 : ℝ) ≤ 1) (div_nonneg ht hx.le)
      (by norm_num only : (1 / 4 : ℝ) + 3 / 4 = 1)
  simp only [Real.one_rpow, one_mul, mul_one] at h
  have hm := mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hx.le (3 / 4))
  rw [Real.div_rpow ht hx.le, mul_div_cancel₀ _ (Real.rpow_pos_of_pos hx (3 / 4)).ne'] at hm
  exact hm

/-- For nonzero x and nonnegative cutoff, evaluate the exponential affine
error-envelope integral exactly. Differentiate its polynomial-exponential primitive
and apply the fundamental theorem of calculus. The endpoint enables error cancellation. -/
private theorem exp_affine_integral (x B : ℝ) (hx : x ≠ 0) {y : ℝ} (hy : 0 ≤ y) :
    (∫ t in Set.Ioc 0 y, Real.exp (-t / x) * (t - B * (1 / 4 + 3 / 4 * (t / x)))) =
      (-(x * (y + x)) + B * (x + 3 / 4 * y)) * Real.exp (-y / x) + x ^ 2 - B * x := by
  have hd (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (-(x * (u + x)) + B * (x + 3 / 4 * u)) * Real.exp (-u / x))
      (Real.exp (-t / x) * (t - B * (1 / 4 + 3 / 4 * (t / x)))) t := by
    have hp :=
      (((hasDerivAt_id t).add (hasDerivAt_const t x)).const_mul x).neg.add
        (((hasDerivAt_const t x).add ((hasDerivAt_id t).const_mul (3 / 4))).const_mul B)
    have he := ((hasDerivAt_id t).neg.div_const x).exp
    have h := hp.mul he
    change
      HasDerivAt (fun u : ℝ ↦ (-(x * (u + x)) + B * (x + 3 / 4 * u)) * Real.exp (-u / x))
        ((-(x * (1 + 0)) + B * (0 + 3 / 4 * 1)) * Real.exp (-t / x) +
          (-(x * (t + x)) + B * (x + 3 / 4 * t)) * (Real.exp (-t / x) * (-1 / x)))
        t at h
    apply h.congr_deriv
    field_simp (discharger :=
      first
      | (norm_num only; done)
      | exact hx)
    ring
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t / x) * (t - B * (1 / 4 + 3 / 4 * (t / x)))) :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const x)).mul
      (continuous_id.sub
        (continuous_const.mul
          (continuous_const.add (continuous_const.mul (continuous_id.div_const x)))))
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hd t) (hc.intervalIntegrable 0 y)
  rw [intervalIntegral.integral_of_le hy] at h
  simp only [neg_zero, zero_div, Real.exp_zero, mul_one, zero_add, mul_zero, add_zero] at h
  nlinarith only [h]

/-- A uniform psi error C t^(3/4), with C≥0, implies exponential finite sum
at least x(1-exp(-y/x))-C x^(3/4) for x>0 and y≥0. Apply the common tangent
envelope to both Abel terms, evaluate its integral, and retain their endpoint cancellation.
This gives a finite, explicit bound without an eventual threshold. -/
theorem exponentialMangoldtSum_lower_of_psi_error {C x y : ℝ} (hC : 0 ≤ C) (hx : 0 < x) (hy : 0 ≤ y)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    x * (1 - Real.exp (-y / x)) - C * x ^ (3 / 4 : ℝ) ≤ exponentialMangoldtSum x y := by
  let B := C * x ^ (3 / 4 : ℝ)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg hx.le _)
  have hl (t : ℝ) (ht : 0 ≤ t) : t - B * (1 / 4 + 3 / 4 * (t / x)) ≤ Chebyshev.psi t := by
    have hp := (abs_le.mp (hpsi t ht)).1
    have htB := mul_le_mul_of_nonneg_left (three_quarter_rpow_le_scaled_affine ht hx) hC
    dsimp only [B]
    nlinarith only [hp, htB]
  have hEnd := mul_le_mul_of_nonneg_left (hl y hy) (Real.exp_pos (-y / x)).le
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t / x)) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const x)
  have hfi :
    MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-t / x) * Chebyshev.psi t) (Set.Ioc 0 y) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (a := (0 : ℝ)) (b := y)
        (by norm_num only) hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hgc : Continuous (fun t : ℝ ↦ Real.exp (-t / x) * (t - B * (1 / 4 + 3 / 4 * (t / x)))) :=
    hc.mul
      (continuous_id.sub
        (continuous_const.mul
          (continuous_const.add (continuous_const.mul (continuous_id.div_const x)))))
  have hgi := hgc.integrableOn_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := y)
  have hInt :=
    MeasureTheory.setIntegral_mono_on (hgi.mono_set Set.Ioc_subset_Icc_self) hfi measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonneg_left (hl t ht.1.le) (Real.exp_pos (-t / x)).le)
  have hInt' := mul_le_mul_of_nonneg_left hInt (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1) hx.le)
  rw [exp_affine_integral x B hx.ne' hy] at hInt'
  have hAlg :
    Real.exp (-y / x) * (y - B * (1 / 4 + 3 / 4 * (y / x))) +
        (1 / x) * ((-(x * (y + x)) + B * (x + 3 / 4 * y)) * Real.exp (-y / x) + x ^ 2 - B * x) =
      x * (1 - Real.exp (-y / x)) - B + 3 / 4 * B * Real.exp (-y / x) := by
    field_simp (discharger :=
      first
      | (norm_num only; done)
      | exact hx.ne')
    ring
  have hNonneg : 0 ≤ 3 / 4 * B * Real.exp (-y / x) :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) hB) (Real.exp_pos _).le
  have hId := exponentialMangoldtSum_eq_psi_integral x hy
  unfold exponentialMangoldtSum at hId ⊢
  change x * (1 - Real.exp (-y / x)) - B ≤ _
  linarith only [hId, hEnd, hInt', hAlg, hNonneg]

/-- Normalize the finite exponential lower bound by sqrt(x), for x>0 and
y≥0. A psi error C t^(3/4) becomes a kernel truncation error C x^(1/4).
Division and real-power identities match the principal Gamma summand normalization. -/
theorem exponentialMangoldtSum_div_sqrt_lower_of_psi_error {C x y : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hy : 0 ≤ y) (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    Real.sqrt x * (1 - Real.exp (-y / x)) - C * x ^ (1 / 4 : ℝ) ≤
      exponentialMangoldtSum x y / Real.sqrt x := by
  have h :=
    div_le_div_of_nonneg_right (exponentialMangoldtSum_lower_of_psi_error hC hx hy hpsi)
      (Real.sqrt_nonneg x)
  have hp : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
    congr 1
    norm_num only
  have he :
    (x * (1 - Real.exp (-y / x)) - C * x ^ (3 / 4 : ℝ)) / Real.sqrt x =
      Real.sqrt x * (1 - Real.exp (-y / x)) - C * x ^ (1 / 4 : ℝ) := by
    calc
      _ = (x / Real.sqrt x) * (1 - Real.exp (-y / x)) - C * (x ^ (3 / 4 : ℝ) / Real.sqrt x) := by
        ring
      _ = _ := by rw [Real.div_sqrt, hp]
  rw [he] at h
  exact h

/-- The finite exponential Mangoldt sum on positive indices not coprime to m.
This is the exact missing-prime-factor contribution for a principal character,
before division by sqrt(x). It retains the real cutoff y. -/
noncomputable def commonFactorExponentialSum (x y : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n ↦ ¬Nat.Coprime n m),
    Real.exp (-(n : ℝ) / x) * ArithmeticFunction.vonMangoldt n

/-- At positive scale and cutoff y≥1, the missing exponential sum for nonzero
modulus m is at most log(m)log(y)/log(2). Its exponential weights lie between
zero and one; the prime-power count bounds the unweighted missing sum.
This gives an explicit finite principal-character level correction. -/
theorem commonFactorExponentialSum_le_log_product {x y : ℝ} (hx : 0 < x) {m : ℕ} (hm : m ≠ 0)
    (hy : 1 ≤ y) : commonFactorExponentialSum x y m ≤ Real.log m * Real.log y / Real.log 2 := by
  classical
  have he :
    commonFactorExponentialSum x y m ≤
      ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n ↦ ¬Nat.Coprime n m),
        ArithmeticFunction.vonMangoldt n := by
    unfold commonFactorExponentialSum
    apply Finset.sum_le_sum
    intro n _hn
    have hExp : Real.exp (-(n : ℝ) / x) ≤ 1 :=
      Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) hx.le)
    exact
      (mul_le_mul_of_nonneg_right hExp ArithmeticFunction.vonMangoldt_nonneg).trans_eq (one_mul _)
  exact he.trans (sum_vonMangoldt_not_coprime_le_log_product hm hy)

/-- A uniform Chebyshev error Ct^(3/4), C≥0, gives the finite exponential sum
at most x(1-exp(-y/x))+Cx^(3/4), for x>0 and y≥0.
Use a shared affine envelope for the Abel endpoint and integral errors and
retain their cancellation. This gives the upper estimate at every finite cutoff. -/
theorem exponentialMangoldtSum_upper_of_psi_error {C x y : ℝ} (hC : 0 ≤ C) (hx : 0 < x) (hy : 0 ≤ y)
    (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    exponentialMangoldtSum x y ≤ x * (1 - Real.exp (-y / x)) + C * x ^ (3 / 4 : ℝ) := by
  let B := C * x ^ (3 / 4 : ℝ)
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg hx.le _)
  have hl (t : ℝ) (ht : 0 ≤ t) : Chebyshev.psi t ≤ t - (-B) * (1 / 4 + 3 / 4 * (t / x)) := by
    have hp := (abs_le.mp (hpsi t ht)).2
    have htB := mul_le_mul_of_nonneg_left (three_quarter_rpow_le_scaled_affine ht hx) hC
    dsimp only [B]
    nlinarith only [hp, htB]
  have hEnd := mul_le_mul_of_nonneg_left (hl y hy) (Real.exp_pos (-y / x)).le
  have hc : Continuous (fun t : ℝ ↦ Real.exp (-t / x)) :=
    Real.continuous_exp.comp (continuous_id.neg.div_const x)
  have hfi :
    MeasureTheory.IntegrableOn (fun t ↦ Real.exp (-t / x) * Chebyshev.psi t) (Set.Ioc 0 y) := by
    have h :=
      integrableOn_mul_sum_Icc ArithmeticFunction.vonMangoldt (m := 0) (a := (0 : ℝ)) (b := y)
        (by norm_num only) hc.integrableOn_Icc
    simp only [← Chebyshev.psi_eq_sum_Icc] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hgc : Continuous (fun t : ℝ ↦ Real.exp (-t / x) * (t - (-B) * (1 / 4 + 3 / 4 * (t / x)))) :=
    hc.mul
      (continuous_id.sub
        (continuous_const.mul
          (continuous_const.add (continuous_const.mul (continuous_id.div_const x)))))
  have hgi := hgc.integrableOn_Icc (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := y)
  have hInt :=
    MeasureTheory.setIntegral_mono_on hfi (hgi.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc
      (fun t ht ↦ mul_le_mul_of_nonneg_left (hl t ht.1.le) (Real.exp_pos (-t / x)).le)
  have hInt' := mul_le_mul_of_nonneg_left hInt (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1) hx.le)
  rw [exp_affine_integral x (-B) hx.ne' hy] at hInt'
  have hAlg :
    Real.exp (-y / x) * (y - (-B) * (1 / 4 + 3 / 4 * (y / x))) +
        (1 / x) *
          ((-(x * (y + x)) + (-B) * (x + 3 / 4 * y)) * Real.exp (-y / x) + x ^ 2 - (-B) * x) =
      x * (1 - Real.exp (-y / x)) + B - 3 / 4 * B * Real.exp (-y / x) := by
    field_simp (discharger :=
      first
      | (norm_num only; done)
      | exact hx.ne')
    ring
  have hNonneg : 0 ≤ 3 / 4 * B * Real.exp (-y / x) :=
    mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 3 / 4) hB) (Real.exp_pos _).le
  have hId := exponentialMangoldtSum_eq_psi_integral x hy
  change exponentialMangoldtSum x y ≤ x * (1 - Real.exp (-y / x)) + B
  linarith only [hId, hEnd, hInt', hAlg, hNonneg]

/-- Normalize the finite exponential upper estimate by sqrt(x), for x>0 and
y≥0. Dropping the negative exponential main term gives sqrt(x)+Cx^(1/4).
The upper bound is independent of cutoff, so it can pass to a convergent series. -/
theorem exponentialMangoldtSum_div_sqrt_upper_of_psi_error {C x y : ℝ} (hC : 0 ≤ C) (hx : 0 < x)
    (hy : 0 ≤ y) (hpsi : ∀ t : ℝ, 0 ≤ t → |Chebyshev.psi t - t| ≤ C * t ^ (3 / 4 : ℝ)) :
    exponentialMangoldtSum x y / Real.sqrt x ≤ Real.sqrt x + C * x ^ (1 / 4 : ℝ) := by
  have h := exponentialMangoldtSum_upper_of_psi_error hC hx hy hpsi
  have hdrop : x * (1 - Real.exp (-y / x)) ≤ x := by nlinarith only [hx, Real.exp_pos (-y / x)]
  have hb : exponentialMangoldtSum x y ≤ x + C * x ^ (3 / 4 : ℝ) := by linarith only [h, hdrop]
  have hd := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg x)
  have hp : x ^ (3 / 4 : ℝ) / Real.sqrt x = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hx]
    congr 1
    norm_num only
  rw [add_div, mul_div_assoc, Real.div_sqrt, hp] at hd
  exact hd

end PseudoPrime.AnalyticNumberTheory.Arithmetic
