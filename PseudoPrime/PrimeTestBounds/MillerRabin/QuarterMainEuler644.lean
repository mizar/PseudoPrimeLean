/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMainReflection644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRecoveryAbel644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCoefficients644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLeftContour570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCap644

/-! # Reflected contour integrals for the section 31 sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 31 kernel times a positive scale power is integrable on the left line. -/
private theorem line_integrable {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  have hd : quarterKernel644.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel644, LLS.PaperStatements.rationalPoleMellinKernel]
    norm_num only [min_def, ite_false]
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip quarterKernel644 (c :=
      (-9 / 16 : ℝ)) (u := x⁻¹)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (inv_pos.mpr hx)
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  exact h

/-- Integrate a nonzero reflected Dirichlet coefficient using the inverse-scale
kernel profile. -/
theorem quarter_dual_term_integral_644 (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (((n : ℝ) * x)⁻¹) : ℂ) := by
  have he (t : ℝ) :
    LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
        (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    calc
      _ =
          quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) :=
        by ring
      _ = _ := by
        rw [LLS.PaperStatements.reflected_term_factor f hn hx]
        ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm,
    quarter_left_kernel_644 (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)]

/-- The inverse-scale arithmetic term of the reflected sixth-pole kernel,
with zero at index zero. -/
noncomputable def quarterDualTerm644 (f : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else
    (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (Analysis.rationalPoleProfile 3 (50 / 107) (2687 / 2000) (((n : ℝ) * x)⁻¹) : ℂ)

/-- For a positive scale, absolute convergence of the Dirichlet series at
17/16 implies summability of the reflected arithmetic terms. Integrate each
term against the left-line kernel and use the summable integral norm bound. -/
theorem quarter_dual_summable_644 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) : Summable (quarterDualTerm644 f x) := by
  let W := fun t : ℝ ↦
    quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hiW : MeasureTheory.Integrable W := line_integrable hx
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
    push_cast
    ring
  have hsum :=
    (MeasureTheory.hasSum_integral_of_summable_integral_norm
        (fun n ↦
          AnalyticNumberTheory.General.integrable_LSeries_term_mul_weight f (17 / 16) n
            (fun t : ℝ ↦ -t) continuous_neg W hiW)
        (AnalyticNumberTheory.General.summable_integral_norm_LSeries_term_mul_weight hs
          (fun t : ℝ ↦ -t) W)).summable
  have h := hsum.mul_left (((1 / (2 * Real.pi) : ℝ) : ℂ))
  apply h.congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero,
      quarterDualTerm644, ite_true]
  · simpa only [W, ← he, quarterDualTerm644, ite_eq_right hn] using
      quarter_dual_term_integral_644 f hn hx

/-- Absolute Dirichlet convergence permits termwise inversion of the reflected contour integral. -/
theorem quarter_dual_lseries_644 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, quarterDualTerm644 f x n := by
  let W := fun t : ℝ ↦
    quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  have hiW : MeasureTheory.Integrable W := line_integrable hx
  have he (t : ℝ) :
    1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) =
      (((17 / 16 : ℝ) : ℂ) + Complex.I * (-t : ℝ)) := by
    push_cast
    ring
  have hi :=
    AnalyticNumberTheory.General.integral_LSeries_mul_weight_eq_tsum hs (fun t : ℝ ↦ -t) W
      continuous_neg hiW
  simp only [← he] at hi
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) * W t) =
      _
  rw [hi, ← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero,
      quarterDualTerm644, ite_true]
  · simpa only [W, quarterDualTerm644, ite_eq_right hn] using quarter_dual_term_integral_644 f hn hx

/-- The reflected logarithmic derivative integral equals the dual Mangoldt series. -/
theorem quarter_dual_logderiv_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, quarterDualTerm644 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := quarter_dual_lseries_644 hx hs
  apply Eq.trans ?_ h
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  have hre : (1 : ℝ) < (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.div_ofNat_re,
      Complex.one_re]
    norm_num only
  dsimp only
  rw [AnalyticNumberTheory.DirichletLFunction.LSeries_mangoldt_eq_neg_logDeriv χ hre]
  simp only [logDeriv, Pi.div_apply, neg_div]

/-- Real character signs and the inverse-scale Mellin transform form the reflected term. -/
private theorem real_term {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x)
    (n : ℕ) :
    (quarterDualTerm644 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (quarterKernel644.transform (((n : ℝ) * x)⁻¹)).re) := by
  by_cases hn : n = 0
  · subst n
    simp only [quarterDualTerm644, ite_true, Complex.zero_re, ArithmeticFunction.map_zero, zero_div,
      zero_mul, mul_zero]
  · have hp : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    rw [quarterDualTerm644, ite_eq_right hn, hp, quarterKernel644,
      LLS.PaperStatements.rationalPole_transform _ _ _ _
        (inv_pos.mpr (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx))]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring

/-- The real part of the normalized reflected logarithmic derivative on the left contour. -/
noncomputable def quarterMainEuler644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
          (quarterKernel644.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re

/-- At positive scale the inverse-scale character series sums to the real left-line integral. -/
theorem quarter_main_euler_hasSum_644 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    HasSum
      (fun n : ℕ ↦
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (quarterKernel644.transform (((n : ℝ) * x)⁻¹)).re))
      (quarterMainEuler644 χ x) := by
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := (quarter_dual_summable_644 hx hs).hasSum
  simp only [Pi.mul_def] at h
  rw [← quarter_dual_logderiv_644 χ hx] at h
  have hr := Complex.reCLM.hasSum h
  exact hr.congr_fun (fun n ↦ (real_term χ hx n).symm)

/-- At scale at least one, the inverse-scale main kernel weight agrees
with the reflected power-log weight used in the arithmetic tail bounds. -/
theorem quarter_main_euler_weight_644 {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (quarterKernel644.transform (((n : ℝ) * x)⁻¹)).re =
      ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 *
          x ^ (-(107 / 100) : ℝ)) *
        (ArithmeticFunction.vonMangoldt n *
          quarterReflectedWeight (2687 / 1000 + Real.log x) n) := by
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, zero_div, zero_mul, zero_mul, mul_zero]
  have hn₁ : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hn₀ := zero_lt_one.trans_le hn₁
  have hx₀ := zero_lt_one.trans_le hx
  have hnx := mul_pos hn₀ hx₀
  have hs : Real.log (((n : ℝ) * x)⁻¹) ≤ 2687 / 1000 := by
    rw [Real.log_inv, Real.log_mul hn₀.ne' hx₀.ne']
    linarith only [Real.log_nonneg hn₁, Real.log_nonneg hx]
  rw [quarter_transform_644 (inv_pos.mpr hnx) hs, Real.log_inv, Real.log_mul hn₀.ne' hx₀.ne']
  have he :
    Real.exp (-((107 / 100) * (2687 / 1000 - -(Real.log n + Real.log x)))) =
      Real.exp (-(107 / 100) * (2687 / 1000)) * (n : ℝ) ^ (-(107 / 100) : ℝ) *
        x ^ (-(107 / 100) : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hx₀, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he, quarterReflectedWeight, Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hn₀.le,
    show (-(157 / 100) : ℝ) = -(1 / 2) + -(107 / 100) by norm_num only, Real.rpow_add hn₀]
  ring

/-- At scale at least one the three reflected contour integrals sum to
the power-log series weighted by the trace of the three characters. -/
theorem quarter_main_euler_trace_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {x : ℝ}
    (hx : 1 ≤ x) :
    let D :=
      (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 * x ^ (-(107 / 100) : ℝ)
    quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x =
      D *
        ∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n *
              quarterReflectedWeight (2687 / 1000 + Real.log x) n) := by
  intro D
  have h₀ := zero_lt_one.trans_le hx
  rw [←
    (((quarter_main_euler_hasSum_644 a h₀).add (quarter_main_euler_hasSum_644 b h₀)).add
        (quarter_main_euler_hasSum_644 c h₀)).tsum_eq,
    ← tsum_mul_left]
  exact
    tsum_congr
      (fun n ↦ by
        dsimp only [D]
        rw [quarter_main_euler_weight_644 hx]
        ring)

/-- Under RH and the trace prefix conditions, the negative sum of the
three reflected main integrals is bounded by the certified right endpoint. -/
theorem quarter_main_euler_endpoint_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r u : ℝ} (hr : r ∈ Set.Icc 316 322) (hu : u ∈ Set.Icc 316 322)
    (hru : r ≤ u)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    -(quarterMainEuler644 a (r ^ 2) + quarterMainEuler644 b (r ^ 2) +
          quarterMainEuler644 c (r ^ 2)) ≤
      reflectedEnvelope644 u - 0.0013281 := by
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hx : (1 : ℝ) ≤ r ^ 2 := one_le_pow₀ hr₁
  rw [quarter_main_euler_trace_644 a b c hx]
  rw [← Real.rpow_natCast_mul (zero_le_one.trans hr₁), Real.log_pow]
  have h := quarter_reflected_endpoint_644 hRH hr hu hru _ ht hp
  dsimp only at h
  norm_num only [Nat.cast_ofNat, zero_sub] at h ⊢
  exact h

/-- At a shifted scale still at least one, the three reflected integrals
share one trace series. The main shift cancels from the logarithmic weight. -/
theorem quarter_shift_euler_trace_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r h : ℝ}
    (hr : 0 < r) (hx : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + h))) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)
    quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x =
      D *
        ∑' n : ℕ,
          ((a n).re + (b n).re + (c n).re) *
            (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight (2 * Real.log r - h) n) := by
  intro x D
  rw [quarter_main_euler_trace_644 a b c hx]
  have hl : 2687 / 1000 + Real.log x = 2 * Real.log r - h := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    norm_num only [Nat.cast_ofNat]
    ring
  rw [hl]
  congr 1
  dsimp only [x, D]
  rw [Real.mul_rpow (sq_nonneg r) (Real.exp_pos _).le, ← Real.rpow_natCast_mul hr.le,
    Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  norm_num only [Nat.cast_ofNat]
  have he :
    Real.exp (-(107 / 100) * (2687 / 1000)) * Real.exp (-(2687 / 1000 + h) * -(107 / 100)) =
      Real.exp ((107 / 100) * h) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ =
        (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) *
          (Real.exp (-(107 / 100) * (2687 / 1000)) *
            Real.exp (-(2687 / 1000 + h) * -(107 / 100))) :=
      by ring_nf
    _ = _ := by
      rw [he]
      norm_num only

/-- At a shifted main scale at least one, the difference between three
level-one integrals and the three character integrals is the trace deficit. -/
theorem quarter_shift_euler_deficit_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r h : ℝ}
    (hr : 0 < r) (hx : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + h))) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)
    3 * quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x -
        (quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x) =
      D *
        ∑' n : ℕ,
          (3 - ((a n).re + (b n).re + (c n).re)) *
            (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight (2 * Real.log r - h) n) := by
  intro x D
  let ψ := (1 : DirichletCharacter ℂ 1)
  let W := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n * quarterReflectedWeight (2 * Real.log r - h) n
  let τ := fun n : ℕ ↦ (a n).re + (b n).re + (c n).re
  have hψ (n : ℕ) : (ψ n).re = 1 := by
    simp only [ψ, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re]
  have h₁ := quarter_shift_euler_trace_644 ψ ψ ψ hr hx
  dsimp only at h₁
  simp only [hψ, show (1 : ℝ) + 1 + 1 = 3 by norm_num only] at h₁
  have h₂ := quarter_shift_euler_trace_644 a b c hr hx
  have hz : Summable W := weight_summable _
  have ht : Summable (fun n ↦ τ n * W n) := by
    apply (hz.norm.mul_left 3).of_norm_bounded
    intro n
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    dsimp only [τ]
    rw [Real.norm_eq_abs]
    have hn (m : ℕ) (χ : DirichletCharacter ℂ m) : |(χ n).re| ≤ 1 :=
      (Complex.abs_re_le_norm _).trans (χ.norm_le_one n)
    have hab := abs_add_le (a n).re (b n).re
    apply (abs_add_le _ _).trans
    linarith only [hab, hn p a, hn q b, hn s c]
  rw [show 3 * quarterMainEuler644 ψ x = D * ∑' n, (3 : ℝ) * W n by linear_combination h₁]
  rw [h₂, ← mul_sub]
  congr 1
  exact ((hz.mul_left 3).tsum_sub ht).symm.trans (tsum_congr fun n ↦ (sub_mul _ _ _).symm)

/-- Under RH and the trace prefix conditions, the level-one deficit in
the actual shifted main integrals is bounded by the scaled tail caps. -/
theorem quarter_shift_euler_loss_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r h : ℝ} (hr : 0 < r)
    (hx : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + h))) (hz : 0 ≤ 2 * Real.log r - h)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
    let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)
    3 * quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x -
        (quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x) ≤
      D *
        (4 *
          ∑ j ∈ Finset.range 6,
            (Nat.choose 5 j : ℝ) * (2 * Real.log r - h) ^ (5 - j) *
              reflectedCapFrom644 99000 j) := by
  dsimp only
  rw [quarter_shift_euler_deficit_644 a b c hr hx]
  exact quarter_shift_deficit_644 hRH hr hz _ ht hp

/-- The three-character deficit relative to level one at a main-kernel shift. -/
noncomputable def quarterShiftLoss644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (r h : ℝ) : ℝ :=
  let x := r ^ 2 * Real.exp (-(2687 / 1000 + h))
  3 * quarterMainEuler644 (1 : DirichletCharacter ℂ 1) x -
    (quarterMainEuler644 a x + quarterMainEuler644 b x + quarterMainEuler644 c x)

/-- The unshifted deficit absorbs part of a negative shifted term. The
factor accounts exactly for the change of scale outside the logarithmic weight. -/
theorem quarter_shift_loss_compare_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r h : ℝ}
    (hr : 0 < r) (hh : 0 ≤ h) (hz : h ≤ 2 * Real.log r)
    (hx₀ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 0)))
    (hx : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + h)))
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3) :
    Real.exp (-((107 / 100) * h)) * quarterShiftLoss644 a b c r h ≤
      quarterShiftLoss644 a b c r 0 := by
  unfold quarterShiftLoss644
  rw [quarter_shift_euler_deficit_644 a b c hr hx, quarter_shift_euler_deficit_644 a b c hr hx₀]
  simp only [mul_zero, Real.exp_zero, mul_one, sub_zero]
  let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ)
  have hD : 0 ≤ D := by
    dsimp only [D]; positivity
  have he (y : ℝ) :
    Real.exp (-((107 / 100) * h)) * (D * Real.exp ((107 / 100) * h) * y) = D * y := by
    rw [← mul_assoc, mul_left_comm, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      one_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_left (quarter_deficit_shift_le_644 hh hz _ ht) hD

/-- The three signed reflected deficits are bounded below by only the
unabsorbed part at shift 0.02 and the loss at shift 1.1. -/
theorem quarter_shift_loss_mix_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hr : 0 < r) (hz : 1 / 50 ≤ 2 * Real.log r) (hx₀ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 0)))
    (hx₁ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 1 / 50)))
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3) :
    let F := quarterShiftLoss644 a b c r
    let ν := 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50)))
    (-ν) * F (1 / 50) - 0.0917 * F (11 / 10) ≤
      1.54 * F 0 - 1.508 * F (1 / 50) - 0.0917 * F (11 / 10) := by
  intro F ν
  have h := quarter_shift_loss_compare_644 a b c hr (by norm_num only) hz hx₀ hx₁ ht
  dsimp only [F, ν]
  linarith only [h]

/-- The coefficient of the unabsorbed first shifted deficit is nonnegative. -/
theorem quarter_shift_loss_coeff_644 : 0 ≤ 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50))) := by
  let t : ℝ := (107 / 100) * (1 / 50)
  change 0 ≤ 1.508 - 1.54 * Real.exp (-t)
  have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (by norm_num only : (0 : ℝ) ≤ 1.508)
  have ht : (1.54 : ℝ) ≤ 1.508 * (t + 1) := by norm_num only [t]
  rw [Real.exp_neg, ← div_eq_mul_inv]
  exact sub_nonneg.mpr ((div_le_iff₀ (Real.exp_pos t)).mpr (ht.trans h))

/-- The scaled unsigned tail bound for a shift, multiplied by four to
account for the largest possible deficit of the trace. -/
noncomputable def quarterShiftCap644 (r h : ℝ) : ℝ :=
  ((107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)) *
    (4 *
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * (2 * Real.log r - h) ^ (5 - j) * reflectedCapFrom644 99000 j)

/-- Under RH and the trace prefix conditions, the signed shifted reflection
is bounded below by the two remaining scaled tail caps. -/
theorem quarter_shift_mix_lower_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r : ℝ} (hr : 0 < r) (hz : 11 / 10 ≤ 2 * Real.log r)
    (hx₀ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 0)))
    (hx₁ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 1 / 50)))
    (hx₂ : 1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + 11 / 10)))
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let F := quarterShiftLoss644 a b c r
    let ν := 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50)))
    (-ν) * quarterShiftCap644 r (1 / 50) - 0.0917 * quarterShiftCap644 r (11 / 10) ≤
      1.54 * F 0 - 1.508 * F (1 / 50) - 0.0917 * F (11 / 10) := by
  intro F ν
  have hz₁ : 1 / 50 ≤ 2 * Real.log r := by linarith only [hz]
  have h₁ : F (1 / 50) ≤ quarterShiftCap644 r (1 / 50) :=
    quarter_shift_euler_loss_644 a b c hRH hr hx₁ (sub_nonneg.mpr hz₁) ht hp
  have h₂ : F (11 / 10) ≤ quarterShiftCap644 r (11 / 10) :=
    quarter_shift_euler_loss_644 a b c hRH hr hx₂ (sub_nonneg.mpr hz) ht hp
  have hmix := quarter_shift_loss_mix_644 a b c hr hz₁ hx₀ hx₁ ht
  exact
    (sub_le_sub (mul_le_mul_of_nonpos_left h₁ (neg_nonpos.mpr quarter_shift_loss_coeff_644))
          (mul_le_mul_of_nonneg_left h₂ (by norm_num only))).trans
      hmix

/-- The three shifted scales in section 122 are all at least one above
radius 316. The bound follows from `exp 4 < 3^4`. -/
theorem quarter_shift_scale_ge_one_644 {r h : ℝ} (hr : 316 ≤ r) (hh : h ≤ 11 / 10) :
    1 ≤ r ^ 2 * Real.exp (-(2687 / 1000 + h)) := by
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
  have h₄ : Real.exp (4 : ℝ) ≤ 3 ^ 4 := by
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  exact
    (Real.exp_le_exp.mpr (by linarith only [hh])).trans
      (h₄.trans (by nlinarith only [hr, sq_nonneg (r - 316)]))

/-- Above radius 316, the signed shifted reflection lower bound needs
only the RH and trace hypotheses. -/
theorem quarter_shift_mix_at_radius_644 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (hRH : RiemannHypothesis) {r : ℝ} (hr : 316 ≤ r)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re ∧ (a n).re + (b n).re + (c n).re ≤ 3)
    (hp :
      ∀ n ∈ Finset.Ioc 0 99000,
        ArithmeticFunction.vonMangoldt n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    let F := quarterShiftLoss644 a b c r
    let ν := 1.508 - 1.54 * Real.exp (-((107 / 100) * (1 / 50)))
    (-ν) * quarterShiftCap644 r (1 / 50) - 0.0917 * quarterShiftCap644 r (11 / 10) ≤
      1.54 * F 0 - 1.508 * F (1 / 50) - 0.0917 * F (11 / 10) := by
  have hr₀ : 0 < r := by linarith only [hr]
  have hl := (Real.le_log_iff_exp_le hr₀).mpr (by linarith only [Real.exp_one_lt_three, hr])
  exact
    quarter_shift_mix_lower_644 a b c hRH hr₀ (by linarith only [hl])
      (quarter_shift_scale_ge_one_644 hr (by norm_num only))
      (quarter_shift_scale_ge_one_644 hr (by norm_num only))
      (quarter_shift_scale_ge_one_644 hr le_rfl) ht hp

end PseudoPrime.PrimeTestBounds.MillerRabin
