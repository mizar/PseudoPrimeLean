/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.CenteredResolventDerivative

/-!
# Inverse-power pole series

Inverse-square multiplicity mass controls all higher inverse powers on a common small ball.
Local termwise differentiation identifies the higher derivatives of zero resolvents.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A pole of norm at least one half has distance at least half its norm from every
point in the radius-one-quarter ball. The reverse triangle inequality gives the comparison.
This common separation permits uniform majorants for higher inverse powers. -/
theorem norm_pole_div_two_le_norm_sub (a z : ℂ) (ha : (1 / 2 : ℝ) ≤ ‖a‖)
    (hz : z ∈ Metric.ball 0 (1 / 4)) : ‖a‖ / 2 ≤ ‖z - a‖ := by
  rw [Metric.mem_ball, dist_zero_right] at hz
  have ht := norm_sub_le z (z - a)
  rw [sub_sub_cancel] at ht
  linarith only [ht, hz, ha]

/-- For a pole of norm at least one half and a point in the radius-one-quarter ball,
the inverse power of degree n+2, weighted by a natural multiplicity, is bounded by
4^ (n+1) times the inverse-square mass at the pole. Separate the square denominator and
bound each additional inverse factor by four. This controls all higher pole series. -/
theorem norm_inversePowerTerm_le (a z : ℂ) (m n : ℕ) (ha : (1 / 2 : ℝ) ≤ ‖a‖)
    (hz : z ∈ Metric.ball 0 (1 / 4)) :
    ‖(m : ℂ) / (z - a) ^ (n + 2)‖ ≤ 4 ^ (n + 1) * ((m : ℝ) / ‖a‖ ^ 2) := by
  have hd := norm_pole_div_two_le_norm_sub a z ha hz
  have hp : 0 < ‖a‖ := by linarith only [ha]
  have hr : 0 < ‖z - a‖ := by linarith only [hd, ha]
  have hquarter : (1 / 4 : ℝ) ≤ ‖z - a‖ := by linarith only [hd, ha]
  have hinv : 1 / ‖z - a‖ ≤ (4 : ℝ) := by
    simpa only [one_div_div, div_one] using
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hquarter
  have hpow := pow_le_pow_left₀ (div_nonneg zero_le_one (norm_nonneg _)) hinv n
  have hsquare : (m : ℝ) / ‖z - a‖ ^ 2 ≤ 4 * ((m : ℝ) / ‖a‖ ^ 2) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hr) (sq_pos_of_pos hp)]
    have hs := mul_le_mul hd hd (div_nonneg (norm_nonneg _) zero_le_two) (norm_nonneg _)
    have hsq : ‖a‖ ^ 2 ≤ 4 * ‖z - a‖ ^ 2 := by nlinarith only [hs]
    have hm := mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    nlinarith only [hm]
  rw [norm_div, Complex.norm_natCast, norm_pow]
  calc
    (m : ℝ) / ‖z - a‖ ^ (n + 2) = ((m : ℝ) / ‖z - a‖ ^ 2) * (1 / ‖z - a‖) ^ n := by
      rw [pow_add, div_mul_eq_div_mul_one_div, one_div_pow]
      ring
    _ ≤ (4 * ((m : ℝ) / ‖a‖ ^ 2)) * 4 ^ n :=
      mul_le_mul hsquare hpow (pow_nonneg (div_nonneg zero_le_one (norm_nonneg _)) _)
        (mul_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
    _ = 4 ^ (n + 1) * ((m : ℝ) / ‖a‖ ^ 2) := by
      rw [pow_succ]; ring

/-- Away from a pole, the multiplicity-weighted inverse power of degree n+2 has
derivative -(n+2) times the inverse power of degree n+3. Differentiate the power and inverse,
then clear the two nonzero denominators explicitly. This is the termwise derivative. -/
theorem hasDerivAt_inversePowerTerm (a z : ℂ) (m n : ℕ) (hne : z - a ≠ 0) :
    HasDerivAt (fun w : ℂ => (m : ℂ) / (w - a) ^ (n + 2))
      (-((n + 2 : ℕ) : ℂ) * (m : ℂ) / (z - a) ^ (n + 3)) z := by
  have h := (((hasDerivAt_id z).sub_const a).pow (n + 2)).inv (pow_ne_zero _ hne)
  have hh := h.const_mul (m : ℂ)
  convert hh using 1
  · simp only [Pi.inv_apply, Pi.pow_apply, id_eq, div_eq_mul_inv]
  · simp only [Pi.pow_apply, id_eq,
      show n + 2 - 1 = n + 1 from Nat.add_sub_assoc (by decide : 1 ≤ 2) n]
    rw [← mul_div_assoc, div_eq_div_iff (pow_ne_zero _ hne) (pow_ne_zero _ (pow_ne_zero _ hne))]
    simp only [show n + 3 = n + 2 + 1 by rfl, show n + 2 = n + 1 + 1 by rfl, pow_succ]
    ring

/-- Summable inverse-square multiplicity mass and pole norms at least one half imply
absolute convergence of every inverse-power series of degree n+2 on the common small ball.
Use the uniform norm majorant. This justifies its value and the base point for differentiation. -/
theorem summable_inversePowerSeries {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (1 / 2 : ℝ) ≤ ‖α i‖) (hm : Summable (fun i => (m i : ℝ) / ‖α i‖ ^ 2)) (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (1 / 4)) : Summable (fun i => (m i : ℂ) / (z - α i) ^ (n + 2)) := by
  exact
    (hm.mul_left (4 ^ (n + 1))).of_norm_bounded
      (fun i => norm_inversePowerTerm_le (α i) z (m i) n (hα i) hz)

/-- For separated poles with summable inverse-square multiplicity mass, the series of
inverse powers of degree n+2 is differentiable throughout the radius-one-quarter ball.
Its derivative is the sum of -(n+2) times the inverse powers of degree n+3. The common
majorant and convergence at zero permit termwise differentiation on the connected ball. -/
theorem hasDerivAt_inversePowerSeries {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (1 / 2 : ℝ) ≤ ‖α i‖) (hm : Summable (fun i => (m i : ℝ) / ‖α i‖ ^ 2)) (n : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (1 / 4)) :
    HasDerivAt (fun w : ℂ => ∑' i, (m i : ℂ) / (w - α i) ^ (n + 2))
      (∑' i, -((n + 2 : ℕ) : ℂ) * (m i : ℂ) / (z - α i) ^ (n + 3)) z := by
  have h0 : (0 : ℂ) ∈ Metric.ball 0 (1 / 4) := by
    rw [Metric.mem_ball, dist_self]
    norm_num only
  have hg :
    ∀ i,
      ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4),
        HasDerivAt (fun w : ℂ => (m i : ℂ) / (w - α i) ^ (n + 2))
          (-((n + 2 : ℕ) : ℂ) * (m i : ℂ) / (w - α i) ^ (n + 3)) w := by
    intro i w hw
    apply hasDerivAt_inversePowerTerm
    apply norm_pos_iff.mp
    have hd := norm_pole_div_two_le_norm_sub (α i) w (hα i) hw
    linarith only [hd, hα i]
  have hb :
    ∀ i,
      ∀ w ∈ Metric.ball (0 : ℂ) (1 / 4),
        ‖-((n + 2 : ℕ) : ℂ) * (m i : ℂ) / (w - α i) ^ (n + 3)‖ ≤
          ((n + 2 : ℕ) : ℝ) * 4 ^ (n + 2) * ((m i : ℝ) / ‖α i‖ ^ 2) := by
    intro i w hw
    rw [mul_div_assoc, norm_mul, norm_neg, Complex.norm_natCast]
    have h :=
      mul_le_mul_of_nonneg_left (norm_inversePowerTerm_le (α i) w (m i) (n + 1) (hα i) hw)
        (Nat.cast_nonneg (n + 2) : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ))
    simpa only [mul_assoc] using h
  exact
    hasDerivAt_tsum_of_isPreconnected (hm.mul_left (((n + 2 : ℕ) : ℝ) * 4 ^ (n + 2)))
      Metric.isOpen_ball (convex_ball (0 : ℂ) (1 / 4)).isPreconnected hg hb h0
      (summable_inversePowerSeries α m hα hm n h0) hz

/-- If a function has the negative inverse-square pole series as its derivative on the
common small ball, its derivative of order n+1 is (-1)^ (n+1) (n+1)! times the inverse-power
series of degree n+2. Assume separated poles and summable inverse-square multiplicity mass.
Induct using local equality of derivatives and termwise differentiation of the higher series.
This identifies all nonconstant moments in completed logarithmic-derivative expansions. -/
theorem iteratedDeriv_eq_inversePowerSeries_of_hasDerivAt {ι : Type*} (α : ι → ℂ) (m : ι → ℕ)
    (hα : ∀ i, (1 / 2 : ℝ) ≤ ‖α i‖) (hm : Summable (fun i => (m i : ℝ) / ‖α i‖ ^ 2)) (f : ℂ → ℂ)
    (hf : ∀ z ∈ Metric.ball 0 (1 / 4), HasDerivAt f (∑' i, -(m i : ℂ) / (z - α i) ^ 2) z) (n : ℕ)
    {z : ℂ} (hz : z ∈ Metric.ball 0 (1 / 4)) :
    iteratedDeriv (n + 1) f z =
      (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) * (∑' i, (m i : ℂ) / (z - α i) ^ (n + 2)) := by
  induction n generalizing z with
  | zero =>
    rw [iteratedDeriv_one, (hf z hz).deriv]
    simp only [zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one, neg_one_mul, ← tsum_neg,
      neg_div]
  | succ n
    ih =>
    have he :
      iteratedDeriv (n + 1) f =ᶠ[nhds z]
        (fun w : ℂ =>
          (-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ) *
            (∑' i, (m i : ℂ) / (w - α i) ^ (n + 2))) := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    have hd :=
      (hasDerivAt_inversePowerSeries α m hα hm n hz).const_mul
        ((-1 : ℂ) ^ (n + 1) * ((n + 1).factorial : ℂ))
    rw [hd.deriv]
    simp only [mul_div_assoc, tsum_mul_left, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

end PseudoPrime.AnalyticNumberTheory.General
