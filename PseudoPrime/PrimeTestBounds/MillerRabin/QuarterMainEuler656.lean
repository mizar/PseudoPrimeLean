/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656
import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedEuler

/-! # Reflected Euler integral for the section 132 main kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On every positive input and every line to the right of the sixth pole,
the inverse Mellin transform is the explicit nonnegative rational-pole
profile. This specializes the existing inversion theorem to the refined
parameters without changing its normalization. -/
theorem quarter_main_inversion_656 {σ u : ℝ} (hσ : 0 < σ + 11 / 10) (hu : 0 < u) :
    Analysis.inverseMellin (quarterKernel656.function) σ u =
      (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) u : ℂ) := by
  change Analysis.inverseMellin (Analysis.rationalPoleFunction 3 (5 / 11) (21 / 16)) σ u = _
  apply Analysis.inverseMellin_rationalPole (m := 3) (by norm_num only) (by norm_num only) _ hu
  norm_num only at hσ ⊢
  exact hσ

/-- The left-line kernel integral equals the original profile at inverse scale. -/
theorem quarter_left_kernel_656 {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) x⁻¹ : ℂ) := by
  have h :=
    quarter_main_inversion_656 (σ := (-9 / 16 : ℝ)) (u := x⁻¹) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  exact h

/-- The section 132 kernel times a positive scale power is integrable on the left line. -/
private theorem line_integrable {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  have hd : quarterKernel656.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel656, LLS.PaperStatements.rationalPoleMellinKernel]
    norm_num only [min_def, ite_false]
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip quarterKernel656 (c :=
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
theorem quarter_dual_term_integral_656 (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (((n : ℝ) * x)⁻¹) : ℂ) := by
  have he (t : ℝ) :
    LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
        (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    calc
      _ =
          quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) :=
        by ring
      _ = _ := by
        rw [LLS.PaperStatements.reflected_term_factor f hn hx]
        ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm,
    quarter_left_kernel_656 (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)]

/-- The inverse-scale arithmetic term of the reflected sixth-pole kernel,
with zero at index zero. -/
noncomputable def quarterDualTerm656 (f : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else
    (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (Analysis.rationalPoleProfile 3 (5 / 11) (21 / 16) (((n : ℝ) * x)⁻¹) : ℂ)

/-- For a positive scale, absolute convergence of the Dirichlet series at
17/16 implies summability of the reflected arithmetic terms. Integrate each
term against the left-line kernel and use the summable integral norm bound. -/
theorem quarter_dual_summable_656 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) : Summable (quarterDualTerm656 f x) := by
  let W := fun t : ℝ ↦
    quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
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
      quarterDualTerm656, ite_true]
  · simpa only [W, ← he, quarterDualTerm656, ite_eq_right hn] using
      quarter_dual_term_integral_656 f hn hx

/-- Absolute Dirichlet convergence permits termwise inversion of the reflected contour integral. -/
theorem quarter_dual_lseries_656 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, quarterDualTerm656 f x n := by
  let W := fun t : ℝ ↦
    quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
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
      quarterDualTerm656, ite_true]
  · simpa only [W, quarterDualTerm656, ite_eq_right hn] using quarter_dual_term_integral_656 f hn hx

/-- The reflected logarithmic derivative integral equals the dual Mangoldt series. -/
theorem quarter_dual_logderiv_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, quarterDualTerm656 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := quarter_dual_lseries_656 hx hs
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
    (quarterDualTerm656 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (quarterKernel656.transform (((n : ℝ) * x)⁻¹)).re) := by
  by_cases hn : n = 0
  · subst n
    simp only [quarterDualTerm656, ite_true, Complex.zero_re, ArithmeticFunction.map_zero, zero_div,
      zero_mul, mul_zero]
  · have hp : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    rw [quarterDualTerm656, ite_eq_right hn, hp, quarterKernel656,
      LLS.PaperStatements.rationalPole_transform _ _ _ _
        (inv_pos.mpr (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx))]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring

/-- The real part of the normalized reflected logarithmic derivative on the left contour. -/
noncomputable def quarterMainEuler656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) : ℝ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
          (quarterKernel656.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re

/-- At positive scale the inverse-scale character series sums to the real left-line integral. -/
theorem quarter_main_euler_hasSum_656 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    HasSum
      (fun n : ℕ ↦
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (quarterKernel656.transform (((n : ℝ) * x)⁻¹)).re))
      (quarterMainEuler656 χ x) := by
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := (quarter_dual_summable_656 hx hs).hasSum
  simp only [Pi.mul_def] at h
  rw [← quarter_dual_logderiv_656 χ hx] at h
  have hr := Complex.reCLM.hasSum h
  exact hr.congr_fun (fun n ↦ (real_term χ hx n).symm)

/-- At scale at least one, the inverse-scale main kernel weight agrees
with the reflected power-log weight used in the arithmetic tail bounds. -/
theorem quarter_main_euler_weight_656 {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (quarterKernel656.transform (((n : ℝ) * x)⁻¹)).re =
      ((11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120 * x ^ (-(11 / 10) : ℝ)) *
        (ArithmeticFunction.vonMangoldt n *
          ((21 / 8 + Real.log x + Real.log n) ^ 5 / (n : ℝ) ^ (8 / 5 : ℝ))) := by
  by_cases hn : n = 0
  · rw [hn, ArithmeticFunction.map_zero, zero_div, zero_mul, zero_mul, mul_zero]
  have hn₁ : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hn)
  have hn₀ := zero_lt_one.trans_le hn₁
  have hx₀ := zero_lt_one.trans_le hx
  have hnx := mul_pos hn₀ hx₀
  have hs : Real.log (((n : ℝ) * x)⁻¹) ≤ 21 / 8 := by
    rw [Real.log_inv, Real.log_mul hn₀.ne' hx₀.ne']
    linarith only [Real.log_nonneg hn₁, Real.log_nonneg hx]
  rw [quarter_transform_656 (inv_pos.mpr hnx) hs, Real.log_inv, Real.log_mul hn₀.ne' hx₀.ne']
  have he :
    Real.exp (-((11 / 10) * (21 / 8 - -(Real.log n + Real.log x)))) =
      Real.exp (-(11 / 10) * (21 / 8)) * (n : ℝ) ^ (-(11 / 10) : ℝ) * x ^ (-(11 / 10) : ℝ) := by
    rw [Real.rpow_def_of_pos hn₀, Real.rpow_def_of_pos hx₀, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he, Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv, ← Real.rpow_neg hn₀.le]
  rw [show (-(8 * 5⁻¹) : ℝ) = -(1 * 2⁻¹) + -(11 * 10⁻¹) by norm_num only, Real.rpow_add hn₀]
  ring

/-- At a positive radius with shifted scale at least one, the real reflected
contour deficit of three characters equals the power-log deficit used in the
section 132 tail estimate. Subtract the four inverse Mellin series termwise. -/
theorem quarter_shift_euler_deficit_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r h : ℝ}
    (hr : 0 < r) (hx : 1 ≤ r ^ 2 * Real.exp (-(21 / 8 + h))) :
    let x := r ^ 2 * Real.exp (-(21 / 8 + h))
    3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) x -
        (quarterMainEuler656 a x + quarterMainEuler656 b x + quarterMainEuler656 c x) =
      quarterAuxReflection656 (fun n ↦ 3 - ((a n).re + (b n).re + (c n).re)) r h := by
  intro x
  let ψ := (1 : DirichletCharacter ℂ 1)
  have h0 : 0 < x := zero_lt_one.trans_le hx
  have hsum :=
    ((quarter_main_euler_hasSum_656 ψ h0).mul_left 3).sub
      (((quarter_main_euler_hasSum_656 a h0).add (quarter_main_euler_hasSum_656 b h0)).add
        (quarter_main_euler_hasSum_656 c h0))
  have hl : 21 / 8 + Real.log x = 2 * Real.log r - h := by
    dsimp only [x]
    rw [Real.log_mul (pow_ne_zero _ hr.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp]
    norm_num only [Nat.cast_ofNat]
    ring
  have hp :
    Real.exp (-(11 / 10) * (21 / 8)) * x ^ (-(11 / 10) : ℝ) =
      r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h) := by
    rw [Real.rpow_def_of_pos h0, ← Real.exp_add, Real.rpow_def_of_pos hr, ← Real.exp_add]
    congr 1
    linarith only [hl]
  rw [← hsum.tsum_eq, quarterAuxReflection656, ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hψ : (ψ n).re = 1 := by
    simp only [ψ, MulChar.one_apply (isUnit_of_subsingleton (n : ZMod 1)), Complex.one_re]
  rw [hψ, quarter_main_euler_weight_656 hx, hl]
  linear_combination
    ((11 / 10 : ℝ) ^ 5 / 120 * (3 - ((a n).re + (b n).re + (c n).re)) *
          ArithmeticFunction.vonMangoldt n *
          (2 * Real.log r - h + Real.log n) ^ 5 /
        (n : ℝ) ^ (8 / 5 : ℝ)) *
      hp

/-- Under RH and agreement on primes through the squared radius, the seven
shifted reflected contour deficits have weighted sum at least -0.00327.
Identify each contour deficit before applying the shared tail estimate. -/
theorem quarter_shift_euler_lower_656 {p q s : ℕ} [NeZero p] [NeZero q] [NeZero s]
    (hRH : RiemannHypothesis) (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {r : ℝ} (hr : r ∈ Set.Icc 322 328)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let x := fun i ↦ r ^ 2 * Real.exp (-(quarterAuxFrequency656 i))
    (-(0.00327 : ℝ)) ≤
      ∑ i,
        quarterAuxCoeff656 i *
          (3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (x i) -
            (quarterMainEuler656 a (x i) + quarterMainEuler656 b (x i) +
              quarterMainEuler656 c (x i))) := by
  intro x
  have hr₀ := (by norm_num only : (0 : ℝ) < 322).trans_le hr.1
  have hX := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) hr.1 2
  have h (i : Fin 7) :=
    quarter_shift_euler_deficit_656 a b c hr₀ (h := (quarterAuxShift656 i : ℝ))
      (quarter_aux_scale_ge_one_656 hX i)
  refine (quarter_aux_character_reflect_656 hRH a b c hr ht ha hb hc).trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (quarterAuxCoeff656 i * ·) (h i).symm

end PseudoPrime.PrimeTestBounds.MillerRabin
