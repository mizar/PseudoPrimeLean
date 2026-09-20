/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Polynomial zeta growth from Euler–Maclaurin summation

A bounded sawtooth correction and its Mellin transform extend the elementary
zeta summation formula to `Re s > -1`, excluding the pole at one.
Analytic continuation uses connectedness of the punctured half-plane.
Bounding the remainder gives polynomial dependence on the norm, with
coefficients determined by the real part and the distance to the pole.
-/

noncomputable section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The periodic "sawtooth" antiderivative of `Int.fract t - 1/2`: on each unit interval
`[n, n+1)`, `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth t = (t-n)(t-n-1)/2`,
a bounded, continuous, piecewise-quadratic
function vanishing at every integer. -/
def zetaSawtooth (t : ℝ) : ℝ :=
  Int.fract t * (Int.fract t - 1) / 2

theorem abs_zetaSawtooth_le (t : ℝ) : |zetaSawtooth t| ≤ 1 / 8 := by
  have h0 : (0 : ℝ) ≤ Int.fract t := Int.fract_nonneg t
  have h1 : Int.fract t < 1 := Int.fract_lt_one t
  rw [zetaSawtooth, abs_le]
  constructor <;> nlinarith only [h0, h1, sq_nonneg (Int.fract t - 1 / 2)]

theorem zetaSawtooth_eq_of_mem_Ico {n : ℤ} {t : ℝ} (ht : t ∈ Set.Ico (n : ℝ) (n + 1)) :
    zetaSawtooth t = (t - n) * (t - n - 1) / 2 := by
  rw [zetaSawtooth, ← Int.self_sub_floor, Int.floor_eq_on_Ico n t ht]

/-- Derivative, on the whole real line (no floor/fract involved), of the quadratic
`(y-n)(y-n-1)/2` that agrees with `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth` on
`[n,n+1)`. -/
theorem hasDerivAt_sawtoothPoly (n : ℤ) (t : ℝ) :
    HasDerivAt (fun y : ℝ => (y - n) * (y - n - 1) / 2) (t - n - 1 / 2) t := by
  have h1 : HasDerivAt (fun y : ℝ => y - (n : ℝ)) 1 t := (hasDerivAt_id t).sub_const _
  have h2 : HasDerivAt (fun y : ℝ => y - (n : ℝ) - 1) 1 t := h1.sub_const _
  have h3 : HasDerivAt (fun y : ℝ => (y - n) * (y - n - 1)) (1 * (t - n - 1) + (t - n) * 1) t :=
    h1.mul h2
  have h4 := h3.div_const 2
  have heq : (1 * (t - (n : ℝ) - 1) + (t - n) * 1) / 2 = t - n - 1 / 2 := by ring
  rwa [heq] at h4

/-- Derivative of `F(t) = t^{-s-1} * ((t-n)(t-n-1)/2)`, the key per-interval antiderivative for
the Euler-Maclaurin integration by parts. -/
theorem hasDerivAt_sawtoothIBP {s : ℂ} (hs : s ≠ -1) (n : ℤ) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ))
      ((-s - 1) * ((t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ)) +
        (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ))
      t := by
  have hr : (-s - 1 : ℂ) ≠ 0 := by
    intro h
    apply hs
    linear_combination -h
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1)) ((-s - 1) * (t : ℂ) ^ (-s - 1 - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht hr
  have h2 :
    HasDerivAt (fun y : ℝ => (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ)) ((t - n - 1 / 2 : ℝ) : ℂ) t :=
    (hasDerivAt_sawtoothPoly n t).ofReal_comp
  have h3 := h1.mul h2
  have heq : (-s - 1 - 1 : ℂ) = -s - 2 := by ring
  rw [heq] at h3
  have heq2 :
    (-s - 1) * (t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ) +
        (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ) =
      (-s - 1) * ((t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ)) +
        (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ) := by
    ring
  rwa [heq2] at h3

theorem continuousOn_sawtoothIBP_deriv {s : ℂ} (n : ℤ) {a : ℝ} (ha : 0 < a) :
    ContinuousOn
      (fun y : ℝ =>
        (-s - 1) * ((y : ℂ) ^ (-s - 2) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ)) +
          (y : ℂ) ^ (-s - 1) * ((y - n - 1 / 2 : ℝ) : ℂ))
      (Set.Icc a (a + 1)) := by
  have hcpow1 : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-s - 2)) (Set.Icc a (a + 1)) := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    exact
      (Complex.continuousAt_ofReal_cpow_const y (-s - 2)
          (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
  have hcpow2 : ContinuousOn (fun y : ℝ => (y : ℂ) ^ (-s - 1)) (Set.Icc a (a + 1)) := by
    intro y hy
    simp only [Set.mem_Icc] at hy
    exact
      (Complex.continuousAt_ofReal_cpow_const y (-s - 1)
          (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
  apply ContinuousOn.add
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.mul hcpow1
    exact Complex.continuous_ofReal.comp_continuousOn (by fun_prop)
  · apply ContinuousOn.mul hcpow2
    exact Complex.continuous_ofReal.comp_continuousOn (by fun_prop)

theorem ae_eq_of_mem_Ico_zetaSawtooth (n : ℤ) (s : ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume),
      t ∈ Set.uIoc (n : ℝ) (n + 1) →
        (t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ) =
          (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  rw [Set.uIoc_of_le (by linarith : (n : ℝ) ≤ n + 1)]
  filter_upwards [(MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (n : ℝ)) (b :=
        n + 1)).mem_iff] with
    t ht₁ ht₂
  have ht₄ := ht₁.mpr ht₂
  have ht₃ : t ∈ Set.Ico (n : ℝ) (n + 1) := ⟨ht₄.1.le, ht₄.2⟩
  rw [zetaSawtooth_eq_of_mem_Ico ht₃]

theorem ae_eq_of_mem_Ico_fract (n : ℤ) (s : ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume),
      t ∈ Set.uIoc (n : ℝ) (n + 1) →
        (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ) =
          (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
  rw [Set.uIoc_of_le (by linarith : (n : ℝ) ≤ n + 1)]
  filter_upwards [(MeasureTheory.Ioo_ae_eq_Ioc (μ := MeasureTheory.volume) (a := (n : ℝ)) (b :=
        n + 1)).mem_iff] with
    t ht₁ ht₂
  have ht₄ := ht₁.mpr ht₂
  have ht₃ : t ∈ Set.Ico (n : ℝ) (n + 1) := ⟨ht₄.1.le, ht₄.2⟩
  rw [← Int.self_sub_floor, Int.floor_eq_on_Ico n t ht₃]

/-- The key per-interval Euler-Maclaurin identity: on `[n,n+1]` (with `n ≥ 1`), the boundary
terms of `∫ t^{-s-1}(fract t - 1/2)` vanish exactly,
since `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth` vanishes at every
integer, giving `∫ t^{-s-1}(fract t - 1/2) = (s+1) ∫ t^{-s-2} ·`
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth t`. -/
theorem integral_fract_sub_half_mul_cpow_eq {s : ℂ} (hs : s ≠ -1) (n : ℤ) (hn : 1 ≤ n) :
    ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) =
      (s + 1) * ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  let F : ℝ → ℂ := fun y => (y : ℂ) ^ (-s - 1) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ)
  have hF : F = fun y : ℝ => (y : ℂ) ^ (-s - 1) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ) := rfl
  let D : ℝ → ℂ := fun y =>
    (-s - 1) * ((y : ℂ) ^ (-s - 2) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ)) +
      (y : ℂ) ^ (-s - 1) * ((y - n - 1 / 2 : ℝ) : ℂ)
  have hD :
    D = fun y : ℝ =>
      (-s - 1) * ((y : ℂ) ^ (-s - 2) * (((y - n) * (y - n - 1) / 2 : ℝ) : ℂ)) +
        (y : ℂ) ^ (-s - 1) * ((y - n - 1 / 2 : ℝ) : ℂ) :=
    rfl
  have hderiv : ∀ t ∈ Set.uIcc (n : ℝ) (n + 1), HasDerivAt F (D t) t := by
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    have ht0 : t ≠ 0 := by
      simp only [Set.mem_Icc] at ht; linarith
    exact hasDerivAt_sawtoothIBP hs n ht0
  have hcont : ContinuousOn D (Set.Icc (n : ℝ) (n + 1)) := continuousOn_sawtoothIBP_deriv n hn1
  have hint : IntervalIntegrable D MeasureTheory.volume (n : ℝ) (n + 1) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hFn1 : F (n + 1 : ℝ) = 0 := by
    simp only [hF, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_intCast, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_add,
      add_sub_cancel_left, sub_self, mul_zero, zero_div]
  have hFn : F (n : ℝ) = 0 := by
    simp only [hF, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub,
      Complex.ofReal_intCast, Complex.ofReal_one, Complex.ofReal_ofNat, sub_self, zero_sub, mul_neg,
      mul_one, neg_zero, zero_div, mul_zero]
  rw [hFn1, hFn, sub_zero] at hFTC
  have hae1 := ae_eq_of_mem_Ico_zetaSawtooth n s
  have hae2 := ae_eq_of_mem_Ico_fract n s
  have hint1 :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.mul
    · intro y hy
      simp only [Set.mem_Icc] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 2)
            (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
    · fun_prop
  have hint2 :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.mul
    · intro y hy
      simp only [Set.mem_Icc] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 1)
            (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
    · fun_prop
  have hI1 :
    ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ) =
      ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) :=
    intervalIntegral.integral_congr_ae hae1
  have hI2 :
    ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ) =
      ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) :=
    intervalIntegral.integral_congr_ae hae2
  have hDeq :
    ∫ t in (n : ℝ)..(n + 1 : ℝ), D t =
      (-s - 1) * (∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) +
        ∫ t in (n : ℝ)..(n + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
    have hstep :
      ∫ t in (n : ℝ)..(n + 1 : ℝ), D t =
        ∫ t in (n : ℝ)..(n + 1 : ℝ),
          ((-s - 1) * ((t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ)) +
            (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ)) := by
      apply intervalIntegral.integral_congr
      intro t _
      rfl
    rw [hstep, intervalIntegral.integral_add (hint1.const_mul _) hint2,
      intervalIntegral.integral_const_mul, hI1, hI2]
  rw [hDeq] at hFTC
  linear_combination hFTC

theorem intervalIntegrable_cpow_mul_sawtooth (n : ℤ) (hn : 1 ≤ n) (s : ℂ) :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hint1 :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * (((t - n) * (t - n - 1) / 2 : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.mul
    · intro y hy
      simp only [Set.mem_Icc] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 2)
            (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
    · fun_prop
  exact
    hint1.congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (ae_eq_of_mem_Ico_zetaSawtooth n s))

theorem intervalIntegrable_cpow_mul_fract (n : ℤ) (hn : 1 ≤ n) (s : ℂ) :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn
  have hint2 :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((t - n - 1 / 2 : ℝ) : ℂ))
      MeasureTheory.volume (n : ℝ) (n + 1) := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by linarith)
    apply ContinuousOn.mul
    · intro y hy
      simp only [Set.mem_Icc] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 1)
            (Or.inr (by linarith : y ≠ (0 : ℝ)))).continuousWithinAt
    · fun_prop
  exact
    hint2.congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr (ae_eq_of_mem_Ico_fract n s))

/-- Integrability of the sawtooth-weighted `t^{-s-2}` integrand over `[1,N]`, for any natural
`N ≥ 1`, obtained by chaining the per-unit-interval integrability across `[1,N]`. -/
theorem intervalIntegrable_cpow_mul_sawtooth_Icc (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
      MeasureTheory.volume 1 (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one]
    exact
      IntervalIntegrable.refl (f := fun t : ℝ => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
        (μ := MeasureTheory.volume) (a := (1 : ℝ))
  | succ k hk
    ih =>
    have hstep :
      IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℝ) :=
      intervalIntegrable_cpow_mul_sawtooth (k : ℤ) (by exact_mod_cast hk) s
    have := ih.trans hstep
    simpa only [Nat.cast_add, Nat.cast_one] using this

/-- Integrability of the fract-weighted `t^{-s-1}` integrand over `[1,N]`, for any natural
`N ≥ 1`. -/
theorem intervalIntegrable_cpow_mul_fract_Icc (N : ℕ) (hN : 1 ≤ N) (s : ℂ) :
    IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      MeasureTheory.volume 1 (N : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [Nat.cast_one]
    exact
      IntervalIntegrable.refl (f := fun t : ℝ =>
        (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ)) (μ := MeasureTheory.volume) (a :=
        (1 : ℝ))
  | succ k hk
    ih =>
    have hstep :
      IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℝ) :=
      intervalIntegrable_cpow_mul_fract (k : ℤ) (by exact_mod_cast hk) s
    have := ih.trans hstep
    simpa only [one_div, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_ofNat, Nat.cast_add,
      Nat.cast_one] using this

/-- The Euler-Maclaurin identity summed over `[1,N]` (any natural `N ≥ 1`), obtained by chaining
the per-unit-interval identity
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.integral_fract_sub_half_mul_cpow_eq`
across consecutive unit intervals. -/
theorem integral_fract_sub_half_mul_cpow_eq_Icc {s : ℂ} (hs : s ≠ -1) (N : ℕ) (hN : 1 ≤ N) :
    ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) =
      (s + 1) * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [one_div, Complex.ofReal_sub, Complex.ofReal_inv, Complex.ofReal_ofNat, Nat.cast_one,
      intervalIntegral.integral_same, mul_zero]
  | succ k hk ih =>
    have hcast : ((k : ℤ) : ℝ) = (k : ℝ) := by norm_cast
    have hstep := integral_fract_sub_half_mul_cpow_eq hs (k : ℤ) (by exact_mod_cast hk)
    rw [hcast] at hstep
    have hintF :
      IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℝ) := by
      have h := intervalIntegrable_cpow_mul_fract (k : ℤ) (by exact_mod_cast hk) s
      rwa [hcast] at h
    have hintS :
      IntervalIntegrable (fun t => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
        MeasureTheory.volume (k : ℝ) (k + 1 : ℝ) := by
      have h := intervalIntegrable_cpow_mul_sawtooth (k : ℤ) (by exact_mod_cast hk) s
      rwa [hcast] at h
    have hadd1 :
      ∫ t in (1 : ℝ)..(k + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) =
        (∫ t in (1 : ℝ)..(k : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ)) +
          ∫ t in (k : ℝ)..(k + 1 : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_cpow_mul_fract_Icc k hk s) hintF]
    have hadd2 :
      ∫ t in (1 : ℝ)..(k + 1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) =
        (∫ t in (1 : ℝ)..(k : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) +
          ∫ t in (k : ℝ)..(k + 1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add_adjacent_intervals
          (intervalIntegrable_cpow_mul_sawtooth_Icc k hk s) hintS]
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) from by
        push_cast; ring] at hadd1 hadd2 hstep
    rw [hadd1, hadd2, ih, hstep]
    ring

/-- The real-valued sawtooth function is measurable, since it is built from
the measurable fractional-part function. -/
theorem measurable_zetaSawtooth : Measurable zetaSawtooth := by
  have h1 : Measurable (Int.fract : ℝ → ℝ) := measurable_fract
  exact (h1.mul (h1.sub_const 1)).div_const 2

/-- The `t^{-s-2} · PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth` integrand is
integrable on `Set.Ioi 1` once `Re s > -1`: it is
dominated by `(1/8) · t^{-(Re s + 2)}`, itself integrable there since `Re s + 2 > 1`. -/
theorem integrableOn_cpow_mul_sawtooth_Ioi {s : ℂ} (hs : -1 < s.re) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
      (Set.Ioi (1 : ℝ)) := by
  have hdom :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 / 8) * t ^ (-(s.re + 2))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-s - 2)) (Set.Ioi (1 : ℝ)) := by
      intro y hy
      simp only [Set.mem_Ioi] at hy
      exact
        (Complex.continuousAt_ofReal_cpow_const y (-s - 2)
            (Or.inr (by linarith))).continuousWithinAt
    have h1 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s - 2))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      hcont.aestronglyMeasurable measurableSet_Ioi
    have h2 :
      MeasureTheory.AEStronglyMeasurable (fun t : ℝ => ((zetaSawtooth t : ℝ) : ℂ))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
      (Complex.continuous_ofReal.measurable.comp measurable_zetaSawtooth).aestronglyMeasurable
    exact h1.mul h2
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < t)]
    have h1 : (-s - 2).re = -(s.re + 2) := by
      simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, neg_add_rev]
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs]
    calc
      t ^ (-(s.re + 2)) * |zetaSawtooth t| ≤ t ^ (-(s.re + 2)) * (1 / 8) :=
        mul_le_mul_of_nonneg_left (abs_zetaSawtooth_le t) (Real.rpow_nonneg (by linarith) _)
      _ = 1 / 8 * t ^ (-(s.re + 2)) := by ring

/-- **Level 2 of the Euler-Maclaurin extension**: the classical `Re s > 0` remainder integral
`∫₁^∞ (fract t - 1/2)·t^{-s-1} dt` equals `(s+1)` times a genuinely absolutely convergent
integral (valid for `Re s > -1`, one order further left), obtained as the `N → ∞` limit of the
finite identity
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.integral_fract_sub_half_mul_cpow_eq_Icc`. -/
theorem tendsto_integral_fract_sub_half_mul_cpow {s : ℂ} (hs : s ≠ -1) (hs' : -1 < s.re) :
    Filter.Tendsto
      (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds
        ((s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))) := by
  have htendstoRHS :
    Filter.Tendsto
      (fun N : ℕ => ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
      Filter.atTop
      (nhds (∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 (integrableOn_cpow_mul_sawtooth_Ioi hs')
      tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr' ?_ (htendstoRHS.const_mul (s + 1))
  filter_upwards [Filter.eventually_ge_atTop 1] with N hN
  exact (integral_fract_sub_half_mul_cpow_eq_Icc hs N hN).symm

/-!
### Preconnectedness of a punctured half-plane

Extend the formula from `Re s > 1` to `{Re s > -1} \ {1}` by the identity
theorem. A polygonal detour avoids the puncture while remaining in the half-plane.
-/

/-- The core geometric fact: if `p` is a genuinely interior point of `[a,b]` (`p ≠ a`, `p ≠ b`)
and `z = a + c • (b - a)` for a non-real scalar `c`, then `p` lies on neither `[a,z]` nor `[z,b]`.
-/
theorem not_mem_segment_offLine {a b : ℂ} (hab : a ≠ b) {c : ℂ} (hc : c.im ≠ 0) {p : ℂ}
    (hp : p ∈ segment ℝ a b) (hpa : p ≠ a) (hpb : p ≠ b) :
    p ∉ segment ℝ a (a + c * (b - a)) ∧ p ∉ segment ℝ (a + c * (b - a)) b := by
  set w : ℂ := b - a with hw_def
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hab.symm
  rw [segment_eq_image'] at hp
  obtain ⟨s, hs01, hps⟩ := hp
  simp only [Set.mem_Icc] at hs01
  simp only [Complex.real_smul] at hps
  have hps' : p = a + (s : ℂ) * w := hps.symm
  have hs0 : s ≠ 0 := by
    rintro rfl; apply hpa; rw [hps']; push_cast; ring
  have hs1 : s ≠ 1 := by
    rintro rfl; apply hpb
    rw [hps', hw_def]; push_cast; ring
  constructor
  · rw [segment_eq_image']
    rintro ⟨t, ht01, hqt⟩
    simp only [Complex.real_smul, show a + c * w - a = c * w from by ring] at hqt
    have heq : a + (t : ℂ) * (c * w) = p := hqt
    rw [hps'] at heq
    have heq2 : (t : ℂ) * c * w = (s : ℂ) * w := by linear_combination heq
    have heq3 : (t : ℂ) * c = (s : ℂ) := mul_right_cancel₀ hw0 heq2
    have himt : ((t : ℂ) * c).im = 0 := by
      rw [heq3]
      simp only [Complex.ofReal_im]
    rw [Complex.mul_im] at himt
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at himt
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp himt with h | h
      · exact h
      · exact absurd h hc
    apply hs0
    have hsz : (s : ℂ) = 0 := by
      rw [← heq3, ht0]
      simp only [Complex.ofReal_zero, zero_mul]
    exact_mod_cast hsz
  · rw [segment_eq_image']
    rintro ⟨t, ht01, hqt⟩
    simp only [Complex.real_smul] at hqt
    have heq : a + c * w + (t : ℂ) * (b - (a + c * w)) = p := hqt
    rw [hps', hw_def] at heq
    have heq2 : c * (b - a) + (t : ℂ) * ((b - a) - c * (b - a)) = (s : ℂ) * (b - a) := by
      linear_combination heq
    have heq3 : c * (1 - (t : ℂ)) + (t : ℂ) = (s : ℂ) := by
      have hcancel : (c * (1 - (t : ℂ)) + (t : ℂ)) * (b - a) = (s : ℂ) * (b - a) := by
        linear_combination heq2
      exact mul_right_cancel₀ hw0 hcancel
    have himt : (c * (1 - (t : ℂ)) + (t : ℂ)).im = 0 := by
      rw [heq3]
      simp only [Complex.ofReal_im]
    have himt2 : c.im * (1 - t) = 0 := by
      have hexp : (c * (1 - (t : ℂ)) + (t : ℂ)).im = c.im * (1 - t) := by
        simp only [Complex.add_im, Complex.mul_im, Complex.sub_im, Complex.one_im,
          Complex.ofReal_im, sub_self, mul_zero, Complex.sub_re, Complex.one_re, Complex.ofReal_re,
          zero_add, add_zero]
      rwa [hexp] at himt
    have ht1 : t = 1 := by
      rcases mul_eq_zero.mp himt2 with h | h
      · exact absurd h hc
      · linarith
    apply hs1
    have hso : (s : ℂ) = 1 := by
      rw [← heq3, ht1]; push_cast; ring
    exact_mod_cast hso

/-- The half-plane `{Re s > -1}` is convex: any point on a segment between two points with
`Re > -1` also has `Re > -1`. -/
theorem re_gt_neg_one_of_mem_segment {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) {q : ℂ}
    (hq : q ∈ segment ℝ a b) : -1 < q.re := by
  rw [segment_eq_image'] at hq
  obtain ⟨u, hu01, hu⟩ := hq
  simp only [Complex.real_smul] at hu
  have hqre : q.re = a.re + u * (b - a).re := by
    rw [← hu]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im,
      Complex.sub_im, zero_mul, sub_zero]
  have hbare : (b - a).re = b.re - a.re := by simp only [Complex.sub_re]
  rw [hbare] at hqre
  rcases hu01.1.lt_or_eq with hu0 | hu0
  · rcases hu01.2.lt_or_eq with hu1 | hu1
    · nlinarith only [ha, hb, hqre, hu0, hu1, mul_pos hu0 (by linarith : (0 : ℝ) < b.re + 1),
        mul_pos (by linarith : (0 : ℝ) < 1 - u) (by linarith : (0 : ℝ) < a.re + 1)]
    · rw [hu1] at hqre; nlinarith
  · rw [← hu0] at hqre; nlinarith

/-- The real part of `a+(1/2+ε*I)*(b-a)` is
`(a.re+b.re)/2-ε*(b.im-a.im)` for arbitrary `a`, `b`, and real `ε`.
This identity is used to keep a later detour inside the half-plane. -/
theorem re_detourPoint_gt {a b : ℂ} (ε : ℝ) :
    (a + ((1 : ℂ) / 2 + (ε : ℝ) * Complex.I) * (b - a)).re =
      (a.re + b.re) / 2 - ε * (b.im - a.im) := by
  simp only [one_div, Complex.add_re, Complex.mul_re, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.sub_re, Complex.add_im,
    Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div, Complex.mul_im, zero_add, Complex.sub_im]
  ring

theorem joinedIn_reGt_neg_one_diff_one {a b : ℂ} (ha : -1 < a.re) (ha1 : a ≠ 1) (hb : -1 < b.re)
    (hb1 : b ≠ 1) : JoinedIn ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) a b := by
  by_cases hab : a = b
  · subst hab; exact JoinedIn.refl ⟨ha, ha1⟩
  by_cases hmem : (1 : ℂ) ∈ segment ℝ a b
  · set δ : ℝ := (a.re + b.re) / 2 + 1 with hδ_def
    have hδ_pos : 0 < δ := by
      rw [hδ_def]; linarith
    set d : ℝ := |b.im - a.im| + 1 with hd_def
    have hd_pos : 0 < d := by
      rw [hd_def]; positivity
    set ε₀ : ℝ := δ / (2 * d) with hε₀_def
    have hε₀_pos : 0 < ε₀ := by
      rw [hε₀_def]; positivity
    have hbound : ∀ ε : ℝ, |ε| ≤ ε₀ → |ε * (b.im - a.im)| < δ := by
      intro ε hε
      rw [abs_mul]
      calc
        |ε| * |b.im - a.im| ≤ ε₀ * |b.im - a.im| := mul_le_mul_of_nonneg_right hε (abs_nonneg _)
        _ < ε₀ * d := by
          apply mul_lt_mul_of_pos_left _ hε₀_pos
          rw [hd_def]; linarith
        _ = δ / 2 := by
          rw [hε₀_def]; field_simp
        _ < δ := by linarith
    have hre : ∀ ε : ℝ, |ε| ≤ ε₀ → -1 < (a + ((1 : ℂ) / 2 + (ε : ℝ) * Complex.I) * (b - a)).re := by
      intro ε hε
      rw [re_detourPoint_gt]
      have := hbound ε hε
      rw [abs_lt] at this
      linarith only [hδ_def, this.2]
    set z₁ : ℂ := a + ((1 : ℂ) / 2 + (ε₀ : ℝ) * Complex.I) * (b - a) with hz1_def
    set z₂ : ℂ := a + ((1 : ℂ) / 2 + (ε₀ / 2 : ℝ) * Complex.I) * (b - a) with hz2_def
    have hz1re : -1 < z₁.re := hre ε₀ (by rw [abs_of_pos hε₀_pos])
    have hz2re : -1 < z₂.re :=
      hre (ε₀ / 2)
        (by
          rw [abs_of_pos (by linarith)]; linarith)
    have hne : z₁ ≠ z₂ := by
      rw [hz1_def, hz2_def]
      intro heq
      have hcancel :
        ((1 : ℂ) / 2 + (ε₀ : ℝ) * Complex.I) = ((1 : ℂ) / 2 + (ε₀ / 2 : ℝ) * Complex.I) :=
        mul_right_cancel₀ (sub_ne_zero.mpr (Ne.symm hab)) (by linear_combination heq)
      have himeq : (ε₀ : ℝ) = ε₀ / 2 := by
        have := congrArg Complex.im hcancel
        simpa only [one_div, Complex.add_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
          Complex.normSq_ofNat, zero_div, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
          Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add, Complex.ofReal_div,
          Complex.ofReal_ofNat, Complex.div_ofNat_re, Complex.div_ofNat_im] using this
      linarith
    have hz1z2 : z₁ ≠ 1 ∨ z₂ ≠ 1 := by
      by_contra h
      push Not at h
      exact hne (h.1.trans h.2.symm)
    have hc1 : ((1 : ℂ) / 2 + (ε₀ : ℝ) * Complex.I).im ≠ 0 := by
      simp only [one_div, Complex.add_im, Complex.inv_im, Complex.im_ofNat, neg_zero,
        Complex.normSq_ofNat, zero_div, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add, ne_eq]
      exact hε₀_pos.ne'
    have hc2 : ((1 : ℂ) / 2 + (ε₀ / 2 : ℝ) * Complex.I).im ≠ 0 := by
      simp only [one_div, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.add_im, Complex.inv_im,
        Complex.im_ofNat, neg_zero, Complex.normSq_ofNat, zero_div, Complex.mul_im,
        Complex.div_ofNat_re, Complex.ofReal_re, Complex.I_im, mul_one, Complex.div_ofNat_im,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, zero_add, ne_eq, div_eq_zero_iff,
        OfNat.ofNat_ne_zero, or_false]
      positivity
    have hp1 : (1 : ℂ) ≠ a := Ne.symm ha1
    have hp2 : (1 : ℂ) ≠ b := Ne.symm hb1
    rcases hz1z2 with hz1ne1 | hz2ne1
    · have hsplit := not_mem_segment_offLine hab hc1 hmem hp1 hp2
      have hJ1 : JoinedIn ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) a z₁ := by
        apply JoinedIn.of_segment_subset
        intro (q : ℂ) (hq : q ∈ segment ℝ a z₁)
        refine ⟨re_gt_neg_one_of_mem_segment ha hz1re hq, fun hq1 => hsplit.1 ?_⟩
        rw [hq1] at hq; exact hq
      have hJ2 : JoinedIn ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) z₁ b := by
        apply JoinedIn.of_segment_subset
        intro (q : ℂ) (hq : q ∈ segment ℝ z₁ b)
        refine ⟨re_gt_neg_one_of_mem_segment hz1re hb hq, fun hq1 => hsplit.2 ?_⟩
        rw [hq1] at hq; exact hq
      exact hJ1.trans hJ2
    · have hsplit := not_mem_segment_offLine hab hc2 hmem hp1 hp2
      have hJ1 : JoinedIn ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) a z₂ := by
        apply JoinedIn.of_segment_subset
        intro (q : ℂ) (hq : q ∈ segment ℝ a z₂)
        refine ⟨re_gt_neg_one_of_mem_segment ha hz2re hq, fun hq1 => hsplit.1 ?_⟩
        rw [hq1] at hq; exact hq
      have hJ2 : JoinedIn ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) z₂ b := by
        apply JoinedIn.of_segment_subset
        intro (q : ℂ) (hq : q ∈ segment ℝ z₂ b)
        refine ⟨re_gt_neg_one_of_mem_segment hz2re hb hq, fun hq1 => hsplit.2 ?_⟩
        rw [hq1] at hq; exact hq
      exact hJ1.trans hJ2
  · apply JoinedIn.of_segment_subset
    intro (q : ℂ) (hq : q ∈ segment ℝ a b)
    refine ⟨re_gt_neg_one_of_mem_segment ha hb hq, fun hq1 => hmem ?_⟩
    rw [hq1] at hq; exact hq

/-- The half-plane `{Re s > -1}` with the pole of `ζ` at `s = 1` removed is preconnected — the
domain on which we will apply the identity theorem to establish the classical remainder-integral
formula for `ζ` beyond `Re s > 1`. -/
theorem isPreconnected_reGt_neg_one_diff_one :
    IsPreconnected ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) := by
  have hpc : IsPathConnected ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
    ⟨2,
      ⟨by
        change (-1 : ℝ) < 2; norm_num only, by
        simp only [Set.mem_singleton_iff]
        intro h
        have h' := congrArg Complex.re h
        change (2 : ℝ) = 1 at h'
        norm_num only at h'⟩,
      fun b hb =>
      joinedIn_reGt_neg_one_diff_one
        (by
          change (-1 : ℝ) < 2; norm_num only)
        (by
          intro h
          have h' := congrArg Complex.re h
          change (2 : ℝ) = 1 at h'
          norm_num only at h')
        hb.1 hb.2⟩
  exact hpc.isConnected.isPreconnected

/-! ### Holomorphicity of the sawtooth remainder integral via the Mellin transform

`J(s) := ∫_{Ioi 1} t^{-s-2} · PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth(t) dt`
is (up to the affine change of variable
`w = -s-1`) the Mellin transform of `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth`
restricted to `Ioi 1` (extended by `0` on
`(0,1]`). Since this extended function is bounded and vanishes near `0`, mathlib's general
Mellin-transform holomorphicity criterion applies directly, with no further estimates needed. -/

/-- `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth`, extended by `0` on `(0,1]`,
viewed as a complex-valued function of `t > 0`. -/
noncomputable def zetaSawtoothIndicator (t : ℝ) : ℂ :=
  if t ≤ 1 then 0 else ((zetaSawtooth t : ℝ) : ℂ)

theorem measurable_zetaSawtoothIndicator : Measurable zetaSawtoothIndicator := by
  unfold zetaSawtoothIndicator
  exact
    Measurable.ite measurableSet_Iic measurable_const
      (Complex.measurable_ofReal.comp measurable_zetaSawtooth)

theorem norm_zetaSawtoothIndicator_le (t : ℝ) : ‖zetaSawtoothIndicator t‖ ≤ 1 / 8 := by
  unfold zetaSawtoothIndicator
  split_ifs with h
  · simp only [norm_zero, one_div, inv_nonneg, Nat.ofNat_nonneg]
  · rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_zetaSawtooth_le t

theorem zetaSawtoothIndicator_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) :
    zetaSawtoothIndicator t = 0 := by
  unfold zetaSawtoothIndicator; rw [ite_eq_left ht]

theorem zetaSawtoothIndicator_eq_of_lt {t : ℝ} (ht : 1 < t) :
    zetaSawtoothIndicator t = ((zetaSawtooth t : ℝ) : ℂ) := by
  unfold zetaSawtoothIndicator; rw [ite_eq_right (not_le.mpr ht)]

theorem locallyIntegrableOn_zetaSawtoothIndicator :
    MeasureTheory.LocallyIntegrableOn zetaSawtoothIndicator (Set.Ioi (0 : ℝ)) := by
  refine (MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).mpr fun K _ hK ↦ ?_
  apply
    MeasureTheory.Integrable.mono'
      (MeasureTheory.integrableOn_const (C := (1 / 8 : ℝ)) hK.measure_lt_top.ne (by finiteness))
  · exact measurable_zetaSawtoothIndicator.aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall fun t => norm_zetaSawtoothIndicator_le t

theorem isBigO_atTop_zetaSawtoothIndicator :
    zetaSawtoothIndicator =O[Filter.atTop] fun t : ℝ => t ^ (-(0 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (1 / 8)
  filter_upwards with t
  rw [neg_zero, Real.rpow_zero, norm_one, mul_one]
  exact norm_zetaSawtoothIndicator_le t

theorem isBigO_nhdsWithin_zetaSawtoothIndicator (b : ℝ) :
    zetaSawtoothIndicator =O[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] fun t : ℝ => t ^ (-b) := by
  have hev : zetaSawtoothIndicator =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] 0 := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num only)),
      self_mem_nhdsWithin] with t ht1 ht2
    exact zetaSawtoothIndicator_eq_zero_of_le_one ht1.le
  exact hev.trans_isBigO (Asymptotics.isBigO_zero (fun t : ℝ => t ^ (-b)) _)

/-- The sawtooth remainder integral, as the Mellin transform of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtoothIndicator`, is
holomorphic in `w` throughout `Re w < 0`
(no lower bound: `PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtoothIndicator` vanishes
identically near `0`, so the "near-zero" growth threshold `b` can be taken as negative as
needed). -/
theorem differentiableAt_mellin_zetaSawtoothIndicator {w : ℂ} (hw1 : w.re < 0) :
    DifferentiableAt ℂ (mellin zetaSawtoothIndicator) w :=
  mellin_differentiableAt_of_isBigO_rpow locallyIntegrableOn_zetaSawtoothIndicator
    isBigO_atTop_zetaSawtoothIndicator (by simpa only using hw1)
    (isBigO_nhdsWithin_zetaSawtoothIndicator (w.re - 1)) (by linarith)

/-- `mellin PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtoothIndicator w`
agrees with the sawtooth remainder integral `J` at
`w = -s-1`, provided `Re s > -1` (so that the integral is genuinely convergent). -/
theorem mellin_zetaSawtoothIndicator_eq {s : ℂ} (hs : -1 < s.re) :
    mellin zetaSawtoothIndicator (-s - 1) =
      ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have hint1 :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1 - 1) • zetaSawtoothIndicator t)
      (Set.Ioc (0 : ℝ) 1) := by
    apply MeasureTheory.integrableOn_zero.congr_fun_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    rw [zetaSawtoothIndicator_eq_zero_of_le_one ht.2, smul_zero]
  have hint2 :
    MeasureTheory.IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s - 1 - 1) • zetaSawtoothIndicator t)
      (Set.Ioi (1 : ℝ)) := by
    have heq :
      (fun t : ℝ =>
          (t : ℂ) ^ (-s - 1 - 1) •
            zetaSawtoothIndicator
              t) =ᶠ[MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))]
        (fun t : ℝ => (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [Set.mem_Ioi] at ht
      rw [zetaSawtoothIndicator_eq_of_lt ht, smul_eq_mul,
        show (-s - 1 - 1 : ℂ) = -s - 2 from by ring]
    rw [MeasureTheory.IntegrableOn, MeasureTheory.integrable_congr heq]
    exact integrableOn_cpow_mul_sawtooth_Ioi hs
  rw [mellin,
    show Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) from by
      ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
      constructor
      · intro ht; by_cases h : t ≤ 1
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (not_le.mp h)
      · rintro (⟨ht, _⟩ | ht)
        · exact ht
        · linarith,
    MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hint1 hint2,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℂ)) fun t ht => by
      rw [zetaSawtoothIndicator_eq_zero_of_le_one ht.2, smul_zero],
    MeasureTheory.integral_zero, zero_add]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [Set.mem_Ioi] at ht
  change
    (t : ℂ) ^ (-s - 1 - 1) • zetaSawtoothIndicator t =
      (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)
  rw [zetaSawtoothIndicator_eq_of_lt ht, smul_eq_mul, show (-s - 1 - 1 : ℂ) = -s - 2 from by ring]

/-- The sawtooth remainder integral
`J(s) := ∫_{Ioi 1} t^{-s-2}·PseudoPrime.AnalyticNumberTheory.RiemannZeta.zetaSawtooth(t) dt` is
holomorphic in `s` throughout `Re s > -1`. -/
theorem differentiableAt_sawtoothRemainder {s : ℂ} (hs1 : -1 < s.re) :
    DifferentiableAt ℂ
      (fun s => ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) s := by
  have hcomp : DifferentiableAt ℂ (fun s : ℂ => -s - 1) s := by fun_prop
  have hd : DifferentiableAt ℂ (mellin zetaSawtoothIndicator) (-s - 1) := by
    apply differentiableAt_mellin_zetaSawtoothIndicator
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  have hcd := hd.comp s hcomp
  have heq :
    (mellin zetaSawtoothIndicator ∘ fun s : ℂ => -s - 1) =ᶠ[nhds s]
      (fun s => ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) := by
    filter_upwards [(Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (show (-1 : ℝ) < s.re by linarith : s ∈ Complex.re ⁻¹' Set.Ioi (-1 : ℝ))] with
      t ht
    exact mellin_zetaSawtoothIndicator_eq ht
  exact hcd.congr_of_eventuallyEq heq.symm

/-! ### Holomorphicity of `ζ` and of the target formula on the punctured half-plane -/

theorem isOpen_reGt_neg_one_diff_one : IsOpen ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
  (isOpen_Ioi.preimage Complex.continuous_re).sdiff isClosed_singleton

/-- `ζ` is analytic throughout `{Re s > -1} \ {1}` (in fact everywhere away from `s = 1`; mathlib
already supplies this directly). -/
theorem analyticOnNhd_riemannZeta_reGt_neg_one_diff_one :
    AnalyticOnNhd ℂ riemannZeta ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_riemannZeta hs.2).differentiableWithinAt)
    isOpen_reGt_neg_one_diff_one

/-- The proposed closed form `s/(s-1) - 1/2 - s(s+1)J(s)` is analytic throughout
`{Re s > -1} \ {1}`: the elementary part `s/(s-1) - 1/2` is analytic away from `s = 1`, and
`J(s)` is analytic on `Re s > -1` by
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.differentiableAt_sawtoothRemainder`. -/
theorem analyticOnNhd_sawtoothFormula_reGt_neg_one_diff_one :
    AnalyticOnNhd ℂ
      (fun s =>
        s / (s - 1) - 1 / 2 -
          s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ))
      ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_reGt_neg_one_diff_one
  intro s hs
  have h1 : DifferentiableAt ℂ (fun s : ℂ => s / (s - 1)) s := by
    apply DifferentiableAt.div (by fun_prop) (by fun_prop)
    exact sub_ne_zero.mpr hs.2
  have h2 :
    DifferentiableAt ℂ
      (fun s => ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) s :=
    differentiableAt_sawtoothRemainder hs.1
  exact
    ((h1.sub_const _).sub
        (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s * (s + 1)) s).mul
          h2))).differentiableWithinAt

/-! ### The classical formula for `Re s > 1`, closing the loop -/

/-- The Abel-summation coefficient sequence picking out `n ↦ 1` for `n ≥ 1` (and `0` at `n = 0`,
as required by `sum_mul_eq_sub_integral_mul₀`). -/
noncomputable def oneFromOne (k : ℕ) : ℂ :=
  if k = 0 then 0 else 1

theorem oneFromOne_zero : oneFromOne 0 = 0 :=
  ite_eq_left rfl

theorem sum_oneFromOne (n : ℕ) : ∑ k ∈ Finset.Icc 0 n, oneFromOne k = (n : ℂ) := by
  have heq : ∀ k, oneFromOne k = 1 - (if k = 0 then (1 : ℂ) else 0) := by
    intro k; unfold oneFromOne; split_ifs <;> ring
  simp_rw [heq]
  rw [Finset.sum_sub_distrib, Finset.sum_const,
    Finset.sum_ite_eq' (Finset.Icc 0 n) 0 (fun _ => (1 : ℂ))]
  simp only [Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one,
    Finset.mem_Icc, Std.le_refl, zero_le, and_self, ↓reduceIte, add_sub_cancel_right]

theorem hasDerivAt_cpow_neg {s : ℂ} (hs0 : s ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s)) (-s * (t : ℂ) ^ (-s - 1)) t :=
  hasDerivAt_ofReal_cpow_const ht (neg_ne_zero.mpr hs0)

theorem continuousOn_deriv_cpow_neg (s : ℂ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (fun t : ℝ => -s * (t : ℂ) ^ (-s - 1)) (Set.Icc a b) := by
  apply ContinuousOn.mul continuousOn_const
  intro t ht
  simp only [Set.mem_Icc] at ht
  exact
    (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
        (Or.inr (by linarith : t ≠ (0 : ℝ)))).continuousWithinAt

/-- The classical finite Abel-summation identity `∑_{k=1}^N k^{-s} = N^{1-s} + s∫_1^N t^{-s-1}⌊t⌋dt`
for any `N ≥ 1`. -/
theorem sum_cpow_eq_sub_integral {s : ℂ} (hs0 : s ≠ 0) (N : ℕ) (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s) =
      (N : ℂ) ^ (-s) * (N : ℂ) +
        s * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-s - 1) * ((⌊t⌋₊ : ℕ) : ℂ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hf_diff :
    ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ), DifferentiableAt ℝ (fun y : ℝ => (y : ℂ) ^ (-s)) t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact (hasDerivAt_cpow_neg hs0 (by linarith : t ≠ (0 : ℝ))).differentiableAt
  have hf_int :
    MeasureTheory.IntegrableOn (deriv (fun y : ℝ => (y : ℂ) ^ (-s))) (Set.Icc (1 : ℝ) (N : ℝ)) := by
    have hderiv_eq :
      ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t = -s * (t : ℂ) ^ (-s - 1) := by
      intro t ht
      simp only [Set.mem_Icc] at ht
      exact (hasDerivAt_cpow_neg hs0 (by linarith : t ≠ (0 : ℝ))).deriv
    exact ((continuousOn_deriv_cpow_neg s zero_lt_one).congr hderiv_eq).integrableOn_Icc
  have hraw := sum_mul_eq_sub_integral_mul₀ oneFromOne oneFromOne_zero (N : ℝ) hf_diff hf_int
  rw [Nat.floor_natCast] at hraw
  push_cast at hraw
  have hlhs :
    ∑ k ∈ Finset.Icc 0 N, (k : ℂ) ^ (-s) * oneFromOne k = ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s) := by
    rw [←
      Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
        (fun k hk0N hk1 => by
          simp only [Finset.mem_Icc] at hk0N hk1
          have hk0 : k = 0 := by omega
          rw [hk0, oneFromOne_zero, mul_zero])]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    unfold oneFromOne
    rw [ite_eq_right (by omega : k ≠ 0), mul_one]
  rw [hlhs, sum_oneFromOne] at hraw
  have hint_eq :
    ∫ t in Set.Ioc (1 : ℝ) (N : ℝ),
        deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, oneFromOne k =
      -s * ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), (t : ℂ) ^ (-s - 1) * ((⌊t⌋₊ : ℕ) : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [Set.mem_Ioc] at ht
    change
      deriv (fun y : ℝ => (y : ℂ) ^ (-s)) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, oneFromOne k =
        -s * ((t : ℂ) ^ (-s - 1) * ((⌊t⌋₊ : ℕ) : ℂ))
    rw [sum_oneFromOne, (hasDerivAt_cpow_neg hs0 (by linarith : t ≠ (0 : ℝ))).deriv]
    ring
  rw [hint_eq] at hraw
  linear_combination hraw

/-- `∫₁^N t^{-s} dt = (N^{1-s} - 1)/(1-s)`, for `s ≠ 1`. -/
theorem integral_cpow_neg {s : ℂ} (hs1 : s ≠ 1) {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in (1 : ℝ)..N, (t : ℂ) ^ (-s) = ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have hderiv :
    ∀ t ∈ Set.uIcc (1 : ℝ) N,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (1 - s) / (1 - s)) ((t : ℂ) ^ (-s)) t := by
    intro t ht
    rw [Set.uIcc_of_le hN] at ht
    simp only [Set.mem_Icc] at ht
    have ht0 : t ≠ (0 : ℝ) := by linarith
    have h := (hasDerivAt_ofReal_cpow_const ht0 h1s).div_const (1 - s)
    have heq : (1 - s) * (t : ℂ) ^ (1 - s - 1) / (1 - s) = (t : ℂ) ^ (-s) := by
      rw [mul_comm, mul_div_assoc, div_self h1s, mul_one, show (1 - s - 1 : ℂ) = -s from by ring]
    rwa [heq] at h
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s)) MeasureTheory.volume 1 N := by
    apply ContinuousOn.intervalIntegrable_of_Icc hN
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr (by linarith))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show ((1 : ℝ) : ℂ) ^ (1 - s) = 1 from by simp only [Complex.ofReal_one, Complex.one_cpow]]
  field_simp

/-- `∫₁^N t^{-s-1} dt = (1 - N^{-s})/s`, for `s ≠ 0`. -/
theorem integral_cpow_neg_sub_one {s : ℂ} (hs0 : s ≠ 0) {N : ℝ} (hN : 1 ≤ N) :
    ∫ t in (1 : ℝ)..N, (t : ℂ) ^ (-s - 1) = (1 - (N : ℂ) ^ (-s)) / s := by
  have hns0 : (-s : ℂ) ≠ 0 := neg_ne_zero.mpr hs0
  have hderiv :
    ∀ t ∈ Set.uIcc (1 : ℝ) N,
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s) / (-s)) ((t : ℂ) ^ (-s - 1)) t := by
    intro t ht
    rw [Set.uIcc_of_le hN] at ht
    simp only [Set.mem_Icc] at ht
    have ht0 : t ≠ (0 : ℝ) := by linarith
    have h := (hasDerivAt_ofReal_cpow_const ht0 hns0).div_const (-s)
    have heq : -s * (t : ℂ) ^ (-s - 1) / (-s) = (t : ℂ) ^ (-s - 1) := by
      rw [mul_comm, mul_div_assoc, div_self hns0, mul_one]
    rwa [heq] at h
  have hint : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s - 1)) MeasureTheory.volume 1 N := by
    apply ContinuousOn.intervalIntegrable_of_Icc hN
    intro t ht
    simp only [Set.mem_Icc] at ht
    exact
      (Complex.continuousAt_ofReal_cpow_const t (-s - 1) (Or.inr (by linarith))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show ((1 : ℝ) : ℂ) ^ (-s) = 1 from by simp only [Complex.ofReal_one, Complex.one_cpow]]
  field_simp
  ring

/-- The classical finite Abel-summation identity, now expressed via the sawtooth remainder
integrand: `∑_{k=1}^N k^{-s} = N^{1-s}/(1-s) + s/(s-1) + N^{-s}/2 - 1/2 -
s∫₁^N t^{-s-1}(fract t - 1/2) dt`. -/
theorem sum_cpow_eq_sawtoothFormula_finite {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (N : ℕ)
    (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s) =
      (N : ℂ) ^ (1 - s) / (1 - s) + s / (s - 1) + (N : ℂ) ^ (-s) / 2 - 1 / 2 -
        s * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hraw := sum_cpow_eq_sub_integral hs0 N hN
  rw [← intervalIntegral.integral_of_le hN1] at hraw
  have hintegrand :
    ∀ t ∈ Set.uIcc (1 : ℝ) (N : ℝ),
      (t : ℂ) ^ (-s - 1) * ((⌊t⌋₊ : ℕ) : ℂ) =
        ((t : ℂ) ^ (-s) - (1 / 2) * (t : ℂ) ^ (-s - 1)) -
          (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ) := by
    intro t ht
    rw [Set.uIcc_of_le hN1] at ht
    simp only [Set.mem_Icc] at ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hcast_ne : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hfloor_real : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      rw [natCast_floor_eq_intCast_floor ht0.le, ← Int.self_sub_floor]; ring
    have hfloor_cast : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast, hfloor_real]
      push_cast
      ring
    have hcpow_add : (t : ℂ) ^ (-s - 1) * (t : ℂ) = (t : ℂ) ^ (-s) := by
      have h := (Complex.cpow_add (-s - 1) 1 hcast_ne).symm
      rw [Complex.cpow_one] at h
      rw [h]
      congr 1; ring
    rw [hfloor_cast, mul_sub, hcpow_add]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hintegrand] at hraw
  have hint1 :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s) - (1 / 2) * (t : ℂ) ^ (-s - 1))
      MeasureTheory.volume 1 (N : ℝ) := by
    apply IntervalIntegrable.sub
    · apply ContinuousOn.intervalIntegrable_of_Icc hN1
      intro t ht
      simp only [Set.mem_Icc] at ht
      exact
        (Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr (by linarith))).continuousWithinAt
    · apply IntervalIntegrable.const_mul
      apply ContinuousOn.intervalIntegrable_of_Icc hN1
      intro t ht
      simp only [Set.mem_Icc] at ht
      exact
        (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
            (Or.inr (by linarith))).continuousWithinAt
  have hint2 :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      MeasureTheory.volume 1 (N : ℝ) :=
    intervalIntegrable_cpow_mul_fract_Icc N hN s
  rw [intervalIntegral.integral_sub hint1 hint2,
    intervalIntegral.integral_sub
      (ContinuousOn.intervalIntegrable_of_Icc hN1 fun t ht => by
        simp only [Set.mem_Icc] at ht
        exact
          (Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr (by linarith))).continuousWithinAt)
      (IntervalIntegrable.const_mul
        (ContinuousOn.intervalIntegrable_of_Icc hN1 fun t ht => by
          simp only [Set.mem_Icc] at ht
          exact
            (Complex.continuousAt_ofReal_cpow_const t (-s - 1)
                (Or.inr (by linarith))).continuousWithinAt)
        (1 / 2 : ℂ)),
    intervalIntegral.integral_const_mul, integral_cpow_neg hs1 hN1,
    integral_cpow_neg_sub_one hs0 hN1] at hraw
  simp only [Complex.ofReal_natCast] at hraw
  have hNcast_ne : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hNpow : (N : ℂ) ^ (-s) * (N : ℂ) = (N : ℂ) ^ (1 - s) := by
    have h := (Complex.cpow_add (-s) 1 hNcast_ne).symm
    rw [Complex.cpow_one] at h
    rw [h]
    congr 1; ring
  rw [hNpow] at hraw
  rw [hraw]
  have h1s : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp
  ring_nf

/-! ### The classical formula for `Re s > 1`, and its extension to the punctured half-plane -/

/-- `(n : ℂ) ^ z → 0` along `ℕ → atTop`, provided `Re z < 0`. -/
theorem tendsto_natCast_cpow_atTop_zero {z : ℂ} (hz : z.re < 0) :
    Filter.Tendsto (fun n : ℕ => (n : ℂ) ^ z) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have heq : (fun n : ℕ => ‖(n : ℂ) ^ z‖) =ᶠ[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ z.re) := by
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact Complex.norm_natCast_cpow_of_pos hn z
  rw [Filter.tendsto_congr' heq]
  have h :=
    (tendsto_rpow_neg_atTop (show (0 : ℝ) < -z.re by linarith)).comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, neg_neg] at h
  exact h

/-- The classical Euler-Maclaurin formula for `ζ`, valid unconditionally for `Re s > 1` (where
the defining Dirichlet series converges): `ζ(s) = s/(s-1) - 1/2 - s(s+1)·J(s)`, with `J(s)` the
sawtooth remainder integral. Obtained as the `N → ∞` limit of the finite identity
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.sum_cpow_eq_sawtoothFormula_finite`. -/
theorem riemannZeta_eq_sawtoothFormula_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s / (s - 1) - 1 / 2 -
        s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have hs0 : s ≠ 0 := fun h => by
    simp only [h, Complex.zero_re] at hs; linarith
  have hs1 : s ≠ 1 := fun h => by
    simp only [h, Complex.one_re] at hs; linarith
  have hsm1 : s ≠ -1 := fun h => by
    simp only [h, Complex.neg_re, Complex.one_re] at hs; linarith
  have hsumtail :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s)) Filter.atTop
      (nhds (riemannZeta s)) := by
    have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) := Complex.summable_one_div_nat_cpow.mpr hs
    have hhasSum : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs]; exact hsumm.hasSum
    have hcongr :
      ∀ N : ℕ,
        ∑ k ∈ Finset.Icc 1 N, (k : ℂ) ^ (-s) = ∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s := by
      intro N
      rw [Nat.range_succ_eq_Icc_zero, ←
        Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1))
          (fun k hk hk1 => by
            simp only [Finset.mem_Icc] at hk hk1
            have hk0 : k = 0 := by omega
            rw [hk0]
            simp only [CharP.cast_eq_zero, ne_eq, hs0, not_false_eq_true, Complex.zero_cpow,
              div_zero])]
      exact Finset.sum_congr rfl fun k _ => by rw [Complex.cpow_neg, one_div]
    simp_rw [hcongr]
    exact hhasSum.tendsto_sum_nat.comp (Filter.tendsto_add_atTop_nat 1)
  have h1 : Filter.Tendsto (fun N : ℕ => (N : ℂ) ^ (1 - s) / (1 - s)) Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_natCast_cpow_atTop_zero (z := 1 - s)
            (by
              simp only [Complex.sub_re, Complex.one_re]; linarith)).div_const
        (1 - s)
    rwa [zero_div] at h
  have h2 : Filter.Tendsto (fun N : ℕ => (N : ℂ) ^ (-s) / 2) Filter.atTop (nhds 0) := by
    have h :=
      (tendsto_natCast_cpow_atTop_zero (z := -s)
            (by
              simp only [Complex.neg_re]; linarith)).div_const
        (2 : ℂ)
    rwa [zero_div] at h
  have h3 :
    Filter.Tendsto
      (fun N : ℕ =>
        s * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds
        (s *
          ((s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)))) :=
    (tendsto_integral_fract_sub_half_mul_cpow hsm1 (by linarith)).const_mul s
  have hc1 : Filter.Tendsto (fun _ : ℕ => s / (s - 1)) Filter.atTop (nhds (s / (s - 1))) :=
    tendsto_const_nhds
  have hc2 : Filter.Tendsto (fun _ : ℕ => (1 : ℂ) / 2) Filter.atTop (nhds ((1 : ℂ) / 2)) :=
    tendsto_const_nhds
  have hL :
    Filter.Tendsto
      (fun N : ℕ =>
        (N : ℂ) ^ (1 - s) / (1 - s) + s / (s - 1) + (N : ℂ) ^ (-s) / 2 - 1 / 2 -
          s * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      Filter.atTop
      (nhds
        (s / (s - 1) - 1 / 2 -
          s *
            ((s + 1) *
              ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)))) := by
    have hpoint :
      (0 : ℂ) + s / (s - 1) + 0 - 1 / 2 -
          s * ((s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) =
        s / (s - 1) - 1 / 2 -
          s *
            ((s + 1) *
              ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) := by
      ring
    rw [← hpoint]
    exact (((h1.add hc1).add h2).sub hc2).sub h3
  have hAB :
    Filter.Tendsto
      (fun N : ℕ =>
        (N : ℂ) ^ (1 - s) / (1 - s) + s / (s - 1) + (N : ℂ) ^ (-s) / 2 - 1 / 2 -
          s * ∫ t in (1 : ℝ)..(N : ℝ), (t : ℂ) ^ (-s - 1) * ((Int.fract t - 1 / 2 : ℝ) : ℂ))
      Filter.atTop (nhds (riemannZeta s)) :=
    Filter.Tendsto.congr'
      (by
        filter_upwards [Filter.eventually_ge_atTop 1] with N hN
        exact sum_cpow_eq_sawtoothFormula_finite hs0 hs1 N hN)
      hsumtail
  have heq := tendsto_nhds_unique hAB hL
  rw [heq]; ring

/-- The classical formula extends, via the identity theorem, from `Re s > 1` to the whole
punctured half-plane `{Re s > -1} \ {1}`. -/
theorem riemannZeta_eq_sawtoothFormula_reGt_neg_one_diff_one {s : ℂ}
    (hs : s ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)})) :
    riemannZeta s =
      s / (s - 1) - 1 / 2 -
        s * (s + 1) * ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) := by
  have h2mem : (2 : ℂ) ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)}) :=
    ⟨by
      change (-1 : ℝ) < 2; norm_num only, by
      simp only [Set.mem_singleton_iff]
      intro h
      have h' := congrArg Complex.re h
      change (2 : ℝ) = 1 at h'
      norm_num only at h'⟩
  have heventually :
    riemannZeta =ᶠ[nhds (2 : ℂ)]
      (fun s =>
        s / (s - 1) - 1 / 2 -
          s * (s + 1) *
            ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_Ioi.preimage Complex.continuous_re
    filter_upwards [hopen.mem_nhds
        (show (2 : ℂ) ∈ {s : ℂ | 1 < s.re} by
          change (1 : ℝ) < 2
          norm_num only)] with
      s hs'
    exact riemannZeta_eq_sawtoothFormula_of_one_lt_re hs'
  exact
    analyticOnNhd_riemannZeta_reGt_neg_one_diff_one.eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_sawtoothFormula_reGt_neg_one_diff_one isPreconnected_reGt_neg_one_diff_one h2mem
      heventually hs

/-! ### A genuinely polynomial (`Im s`-uniform) bound on `‖ζ‖` for fixed `Re s > -1` -/

/-- A bound on the sawtooth remainder integral `J(s)`, depending only on `σ = Re s` (in
particular, uniform in `Im s`): the same pointwise domination used to establish `J`'s
integrability in
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.integrableOn_cpow_mul_sawtooth_Ioi`. -/
noncomputable def sawtoothRemainderBound (σ : ℝ) : ℝ :=
  ∫ t in Set.Ioi (1 : ℝ), (1 / 8 : ℝ) * t ^ (-(σ + 2))

theorem norm_sawtoothRemainder_le {s : ℂ} (hs : -1 < s.re) :
    ‖∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤
      sawtoothRemainderBound s.re := by
  have hdom :
    MeasureTheory.IntegrableOn (fun t : ℝ => (1 / 8 : ℝ) * t ^ (-(s.re + 2))) (Set.Ioi (1 : ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  calc
    ‖∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ ≤
        ∫ t in Set.Ioi (1 : ℝ), ‖(t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ)‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ sawtoothRemainderBound s.re := by
      apply MeasureTheory.integral_mono_of_nonneg
      · filter_upwards with t using norm_nonneg _
      · exact hdom
      · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [Set.mem_Ioi] at ht
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : (0 : ℝ) < t)]
        have h1 : (-s - 2).re = -(s.re + 2) := by
          simp only [Complex.sub_re, Complex.neg_re, Complex.re_ofNat, neg_add_rev]
          ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs]
        calc
          t ^ (-(s.re + 2)) * |zetaSawtooth t| ≤ t ^ (-(s.re + 2)) * (1 / 8) :=
            mul_le_mul_of_nonneg_left (abs_zetaSawtooth_le t) (Real.rpow_nonneg (by linarith) _)
          _ = 1 / 8 * t ^ (-(s.re + 2)) := by ring

theorem sawtoothRemainderBound_nonneg (σ : ℝ) : 0 ≤ sawtoothRemainderBound σ := by
  unfold sawtoothRemainderBound
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  simp only [Set.mem_Ioi] at ht
  positivity

/-- On `(-1,∞)`, the sawtooth remainder bound is antitone: if `-1 < a ≤ b`,
its value at `b` is at most its value at `a`. Compare the defining integrands. -/
theorem sawtoothRemainderBound_antitone {a b : ℝ} (ha : -1 < a) (hab : a ≤ b) :
    sawtoothRemainderBound b ≤ sawtoothRemainderBound a := by
  unfold sawtoothRemainderBound
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    positivity
  · exact (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
  · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    have hexp : -(b + 2) ≤ -(a + 2) := by linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht.le hexp) (by norm_num only)

/-- On `Re s > -1`, away from one, the zeta norm is bounded using a quadratic
norm term and the explicit pole term `‖s‖/‖s-1‖`. The remainder coefficient
depends only on the real part, not the imaginary part. -/
theorem norm_riemannZeta_le_of_reGt_neg_one_diff_one {s : ℂ}
    (hs : s ∈ ({s : ℂ | -1 < s.re} \ {(1 : ℂ)})) :
    ‖riemannZeta s‖ ≤ ‖s‖ / ‖s - 1‖ + 1 / 2 + ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re := by
  rw [riemannZeta_eq_sawtoothFormula_reGt_neg_one_diff_one hs]
  set J : ℂ := ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) ^ (-s - 2) * ((zetaSawtooth t : ℝ) : ℂ) with hJ_def
  have hstep1 :
    ‖s / (s - 1) - 1 / 2 - s * (s + 1) * J‖ ≤ ‖s / (s - 1) - 1 / 2‖ + ‖s * (s + 1) * J‖ :=
    norm_sub_le _ _
  have hstep2 : ‖s / (s - 1) - 1 / 2‖ ≤ ‖s / (s - 1)‖ + ‖(1 : ℂ) / 2‖ := norm_sub_le _ _
  have hstep3 : ‖s * (s + 1) * J‖ ≤ ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re := by
    rw [norm_mul, norm_mul]
    have hb : ‖s + 1‖ ≤ ‖s‖ + 1 := by
      calc
        ‖s + 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖s‖ + 1 := by rw [norm_one]
    have hc : ‖J‖ ≤ sawtoothRemainderBound s.re := by
      rw [hJ_def]; exact norm_sawtoothRemainder_le hs.1
    exact
      mul_le_mul (mul_le_mul_of_nonneg_left hb (norm_nonneg s)) hc (norm_nonneg _) (by positivity)
  have h1 : ‖s / (s - 1)‖ = ‖s‖ / ‖s - 1‖ := norm_div _ _
  have h2 : ‖(1 : ℂ) / 2‖ = (1 : ℝ) / 2 := by
    rw [norm_div, norm_one]
    norm_num only [Complex.norm_ofNat]
  calc
    ‖s / (s - 1) - 1 / 2 - s * (s + 1) * J‖ ≤ ‖s / (s - 1) - 1 / 2‖ + ‖s * (s + 1) * J‖ := hstep1
    _ ≤ (‖s / (s - 1)‖ + ‖(1 : ℂ) / 2‖) + ‖s * (s + 1) * J‖ := add_le_add hstep2 (le_refl _)
    _ ≤ ‖s‖ / ‖s - 1‖ + 1 / 2 + ‖s‖ * (‖s‖ + 1) * sawtoothRemainderBound s.re := by
      rw [h1, h2]; exact add_le_add (le_refl _) hstep3

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
