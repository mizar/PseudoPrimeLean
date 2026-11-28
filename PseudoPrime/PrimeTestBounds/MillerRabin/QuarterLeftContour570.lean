/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTriple570
public import PseudoPrime.LLS.PaperStatements.ReciprocalGapReflectedEuler
public import PseudoPrime.LLS.PaperStatements.TriangularConductorFormula

/-! # Reflected contour integrals for the section 31 sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The left-line kernel integral equals the original profile at inverse scale. -/
theorem left_integral_570 {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ) := by
  have h :=
    Analysis.inverseMellin_rationalPole (m := 3) (a := (25 / 51 : ℝ)) (c := (7 / 5 : ℝ)) (σ :=
      (-9 / 16 : ℝ)) (by norm_num only) (by norm_num only) (by norm_num only) (inv_pos.mpr hx)
  unfold Analysis.inverseMellin at h
  simp only [Complex.ofReal_inv, Complex.cpow_neg, Complex.inv_cpow_ofReal_nonneg hx.le,
    inv_inv] at h
  exact h

/-- The section 31 kernel times a positive scale power is integrable on the left line. -/
private theorem line_integrable {x : ℝ} (hx : 0 < x) :
    MeasureTheory.Integrable
      (fun t : ℝ ↦
        quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
  have hd : quarterKernel570.delta = (1 / 8 : ℝ) := by
    norm_num only [quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    norm_num only [min_def, ite_false]
  have h :=
    LLS.PaperStatements.MellinKernel.integrable_inverse_in_strip quarterKernel570 (c :=
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
theorem term_integral_570 (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (((n : ℝ) * x)⁻¹) : ℂ) := by
  have he (t : ℝ) :
    LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
        (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) =
      (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
        (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
          (((n : ℝ) * x : ℝ) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) := by
    calc
      _ =
          quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (LSeries.term f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) n *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) :=
        by ring
      _ = _ := by
        rw [LLS.PaperStatements.reflected_term_factor f hn hx]
        ring
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_const_mul, mul_left_comm,
    left_integral_570 (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx)]

/-- The inverse-scale arithmetic term of the reflected sixth-pole kernel,
with zero at index zero. -/
noncomputable def dualTerm570 (f : ℕ → ℂ) (x : ℝ) (n : ℕ) : ℂ :=
  if n = 0 then 0
  else
    (f n / (n : ℂ) ^ (1 / 2 : ℂ)) *
      (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (((n : ℝ) * x)⁻¹) : ℂ)

/-- For a positive scale, absolute convergence of the Dirichlet series at
17/16 implies summability of the reflected arithmetic terms. Integrate each
term against the left-line kernel and use the summable integral norm bound. -/
theorem dual_summable_570 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) : Summable (dualTerm570 f x) := by
  let W := fun t : ℝ ↦
    quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
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
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero, dualTerm570,
      ite_true]
  · simpa only [W, ← he, dualTerm570, ite_eq_right hn] using term_integral_570 f hn hx

/-- Absolute Dirichlet convergence permits termwise inversion of the reflected contour integral. -/
theorem lseries_integral_570 {f : ℕ → ℂ} {x : ℝ} (hx : 0 < x)
    (hs : LSeriesSummable f (((17 / 16 : ℝ) : ℂ))) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          LSeries f (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, dualTerm570 f x n := by
  let W := fun t : ℝ ↦
    quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
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
    simp only [LSeries.term_zero, zero_mul, MeasureTheory.integral_zero, mul_zero, dualTerm570,
      ite_true]
  · simpa only [W, dualTerm570, ite_eq_right hn] using term_integral_570 f hn hx

/-- The reflected logarithmic derivative integral equals the dual Mangoldt series. -/
theorem logDeriv_integral_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      ∑' n : ℕ, dualTerm570 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n := by
  have hs :
    LSeriesSummable (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (((17 / 16 : ℝ) : ℂ)) :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := lseries_integral_570 hx hs
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
    (dualTerm570 (fun n ↦ χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) x n).re =
      (χ n).re *
        (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          (quarterKernel570.transform (((n : ℝ) * x)⁻¹)).re) := by
  by_cases hn : n = 0
  · subst n
    simp only [dualTerm570, ite_true, Complex.zero_re, ArithmeticFunction.map_zero, zero_div,
      zero_mul, mul_zero]
  · have hp : (n : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt (n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
      push_cast
      rfl
    rw [dualTerm570, ite_eq_right hn, hp, quarterKernel570,
      LLS.PaperStatements.rationalPole_transform _ _ _ _
        (inv_pos.mpr (mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) hx))]
    simp only [div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring

/-- The real part of the normalized reflected logarithmic derivative on the left contour. -/
noncomputable def reflectedIntegral570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ) :
    ℝ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.LFunction (1 / 2 - (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)) *
          (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))).re

/-- At positive scale the inverse-scale character series sums to the real left-line integral. -/
theorem reflected_hasSum_570 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ} (hx : 0 < x) :
    HasSum
      (fun n : ℕ ↦
        (χ n).re *
          (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
            (quarterKernel570.transform (((n : ℝ) * x)⁻¹)).re))
      (reflectedIntegral570 χ x) := by
  have hs :=
    χ.LSeriesSummable_twist_vonMangoldt
      (show (1 : ℝ) < (((17 / 16 : ℝ) : ℂ)).re by norm_num only [Complex.ofReal_re])
  have h := (dual_summable_570 hx hs).hasSum
  simp only [Pi.mul_def] at h
  rw [← logDeriv_integral_570 χ hx] at h
  have hr := Complex.reCLM.hasSum h
  exact hr.congr_fun (fun n ↦ (real_term χ hx n).symm)

/-- For three characters satisfying the prime-prefix and sign conditions, the negative
sum of their reflected integrals at a square cutoff is below minus 0.0273 throughout
the section 31 radius interval. Add the three absolutely convergent kernel series. -/
theorem reflected_integrals_lt_570 (hRH : RiemannHypothesis) {p q s : ℕ} [NeZero p] [NeZero q]
    [NeZero s] {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    -(reflectedIntegral570 a (r ^ 2) + reflectedIntegral570 b (r ^ 2) +
          reflectedIntegral570 c (r ^ 2)) <
      -(273 / 10000) := by
  have hx := sq_pos_of_pos (show 0 < r by linarith only [hl])
  have h :=
    ((reflected_hasSum_570 a hx).add (reflected_hasSum_570 b hx)).add (reflected_hasSum_570 c hx)
  have he := h.tsum_eq
  simp only [← add_mul] at he
  rw [← he]
  exact reflected_triple_kernel_570 hRH hl hu a b c ht hA hB hC

/-- Reflect the completed left contour and identify the exact inverse-scale conductor term. -/
theorem left_reflection_570 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ) +
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              (quarterKernel570.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))) := by
  let K := quarterKernel570
  let w := fun t : ℝ ↦
    K.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
      (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) * w t
  let C := fun t : ℝ ↦ Complex.log q * w t
  let R := fun t : ℝ ↦ logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) * w t
  have hd : K.delta = (1 / 8 : ℝ) := by
    norm_num only [K, quarterKernel570, LLS.PaperStatements.rationalPoleMellinKernel]
    apply min_eq_right
    norm_num only
  have hF :=
    LLS.PaperStatements.MellinKernel.integrable_completed_left_line K hp hne hinv (c := -9 / 16)
      (x := x)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) (by norm_num only) hx
  have hC :=
    LLS.PaperStatements.MellinKernel.integrable_logWeighted_power_line K (c := -9 / 16) (x := x)
      (F := fun _ : ℝ ↦ Complex.log q) (A := ‖Complex.log q‖)
      (by
        rw [hd]; norm_num only)
      (by
        rw [hd]; norm_num only)
      (by norm_num only) hx MeasureTheory.aestronglyMeasurable_const
      (fun t ↦ by
        have hlog : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
        nlinarith only [hlog, norm_nonneg (Complex.log (q : ℂ))])
  simp only [mul_assoc] at hC
  change MeasureTheory.Integrable F at hF
  change MeasureTheory.Integrable C at hC
  have he (t : ℝ) : F t = C t + R t := by
    dsimp only [F, C, R]
    rw [LLS.PaperStatements.triangular18_completed_left_reflection hp hne hinv t, add_mul]
  have hR : MeasureTheory.Integrable R :=
    (hF.sub hC).congr
      (MeasureTheory.ae_of_all _ (fun t ↦ by rw [Pi.sub_apply, he, add_sub_cancel_left]))
  have hi : (∫ t : ℝ, F t) = (∫ t : ℝ, C t) + ∫ t : ℝ, R t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
      MeasureTheory.integral_add hC hR]
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, F t) = _
  rw [hi, mul_add]
  have hcint :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, C t) =
      Complex.log q * (Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) x⁻¹ : ℂ) := by
    dsimp only [C, w, K]
    rw [MeasureTheory.integral_const_mul]
    rw [← mul_assoc, mul_comm (((1 / (2 * Real.pi) : ℝ) : ℂ)) (Complex.log q), mul_assoc,
      left_integral_570 hx]
  rw [hcint]

end PseudoPrime.PrimeTestBounds.MillerRabin
