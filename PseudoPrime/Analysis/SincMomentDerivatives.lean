/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SineMajorant
import all PseudoPrime.Analysis.SineMajorant
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Derivative bounds for the shifted cosine majorant in the fixed moments -/

public section

namespace PseudoPrime.Analysis

/-- The numerator common to the two fixed moment integrands. -/
noncomputable def sincMomentNumerator (z : ℝ) : ℝ :=
  sineMajorant z + sineMajorantShift

/-- The zeroth derivative uses the uniform value bound. For positive orders the
two cosine frequencies contribute their amplitudes times their frequencies to that power. -/
def sincMomentAmplitude (n : ℕ) : ℚ :=
  if n = 0 then 9 / 8 else 7 / 18 * 2 ^ n + 1 / 18 * 4 ^ n

/-- All orders of the shifted numerator are continuously differentiable. -/
theorem contDiff_sincMomentNumerator (n : ℕ) : ContDiff ℝ n sincMomentNumerator := by
  unfold sincMomentNumerator sineMajorant
  fun_prop

private theorem cos_frequency_bound (n : ℕ) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    |iteratedDeriv n (fun t ↦ Real.cos (c * t)) x| ≤ c ^ n := by
  rw [iteratedDeriv_comp_const_mul Real.contDiff_cos c, abs_mul, abs_of_nonneg (pow_nonneg hc n)]
  exact
    (mul_le_mul_of_nonneg_left (Real.abs_iteratedDeriv_cos_le_one n _) (pow_nonneg hc n)).trans
      (le_of_eq (mul_one _))

/-- For every order n the absolute derivative of the shifted numerator is bounded by
the rational amplitude. In particular this supplies orders zero through four for Simpson cells. -/
theorem abs_iteratedDeriv_sincNumerator (n : ℕ) (x : ℝ) :
    |iteratedDeriv n sincMomentNumerator x| ≤ (sincMomentAmplitude n : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp only [iteratedDeriv_zero, sincMomentNumerator, sincMomentAmplitude, ↓reduceIte,
      Rat.cast_div, Rat.cast_ofNat]
    apply abs_le.mpr
    have hl := (abs_nonneg _).trans (abs_sin_le_majorant x)
    constructor <;>
      linarith only [hl, sineMajorant_le_one x, sineMajorantShift_bounds.1,
        sineMajorantShift_bounds.2]
  have he :
    sincMomentNumerator = fun z ↦
      (2 / 3 + sineMajorantShift) - (7 / 18 * Real.cos (2 * z)) - (1 / 18 * Real.cos (4 * z)) := by
    funext z
    unfold sincMomentNumerator sineMajorant
    ring
  rw [he, iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
    iteratedDeriv_fun_sub (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_const, hn, ↓reduceIte, zero_sub, iteratedDeriv_const_mul_field,
    sincMomentAmplitude, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_one]
  have h2 := abs_le.mp (cos_frequency_bound n (by norm_num only : (0 : ℝ) ≤ 2) x)
  have h4 := abs_le.mp (cos_frequency_bound n (by norm_num only : (0 : ℝ) ≤ 4) x)
  exact abs_le.mpr ⟨by linarith only [h2.2, h4.2], by linarith only [h2.1, h4.1]⟩

/-- Harmonic shift H_(n+1)-1 for the logarithmic moment. -/
def momentLogShift : ℕ → ℚ
  | 0 => 0
  | n + 1 => momentLogShift n + 1 / (n + 2 : ℚ)

/-- Formula for each derivative of the common weight (s log x + t)/x² at positive x. -/
noncomputable def momentWeightTerm (n : ℕ) (s t x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * (n + 1).factorial * ((s * Real.log x + t) - s * (momentLogShift n : ℝ)) /
    x ^ (n + 2)

/-- Differentiating increases the factorial and adds one reciprocal to the harmonic shift. -/
theorem hasDerivAt_momentWeightTerm (n : ℕ) (s t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (momentWeightTerm n s t) (momentWeightTerm (n + 1) s t x) x := by
  have hlog :=
    (((Real.hasDerivAt_log hx.ne').const_mul s).add_const t).sub_const (s * (momentLogShift n : ℝ))
  have h :=
    (hlog.const_mul ((-1 : ℝ) ^ n * (n + 1).factorial)).div ((hasDerivAt_id x).pow (n + 2))
      (pow_ne_zero _ hx.ne')
  apply h.congr_deriv
  simp only [momentWeightTerm, momentLogShift, Rat.cast_add, Rat.cast_div, Rat.cast_one,
    Rat.cast_natCast, Rat.cast_ofNat, id_eq, Pi.pow_apply, Nat.factorial_succ (n + 1), Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  have hn : (n : ℝ) + 2 ≠ 0 := ne_of_gt (by linarith only [Nat.cast_nonneg (α := ℝ) n])
  simp only [show n + 2 - 1 = n + 1 from rfl, pow_succ, mul_one]
  field_simp [hx.ne', hn]
  ring

/-- On the positive half-line the recurrence computes the iterated derivatives of the
initial weight. Local equality suffices to differentiate at each positive point. -/
theorem iteratedDeriv_momentWeightTerm (n : ℕ) (s t : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (momentWeightTerm 0 s t) x = momentWeightTerm n s t x := by
  induction n generalizing x with
  | zero => exact congrFun (iteratedDeriv_zero) x
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h : iteratedDeriv n (momentWeightTerm 0 s t) =ᶠ[nhds x] momentWeightTerm n s t := by
      filter_upwards [lt_mem_nhds hx] with y hy
      exact ih hy
    exact h.deriv_eq.trans (hasDerivAt_momentWeightTerm n s t hx).deriv

/-- The product rule bounds the fourth derivative of either moment integrand by five
terms. The weight factor uses its explicit derivative at the integration point. -/
theorem sincMoment_fourth_le (s t : ℝ) {x : ℝ} (hx : 0 < x) :
    |iteratedDeriv 4 (sincMomentNumerator * momentWeightTerm 0 s t) x| ≤
      ∑ i ∈ Finset.range 5,
        (Nat.choose 4 i : ℝ) * (sincMomentAmplitude i : ℝ) * |momentWeightTerm (4 - i) s t x| := by
  have hw : ContDiffAt ℝ 4 (momentWeightTerm 0 s t) x := by
    unfold momentWeightTerm
    fun_prop (disch :=
      first
      | exact hx.ne'
      | exact pow_ne_zero _ hx.ne')
  rw [iteratedDeriv_mul (contDiff_sincMomentNumerator 4).contDiffAt hw]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), iteratedDeriv_momentWeightTerm _ s t hx]
  exact
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (abs_iteratedDeriv_sincNumerator i x) (Nat.cast_nonneg _))
      (abs_nonneg _)

end PseudoPrime.Analysis
