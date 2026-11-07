/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePoisson

/-! # Majorants for differentiated Poisson resolvents -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive pole distance the absolute first derivative of the Poisson
resolvent is bounded by the inverse quadratic denominator. This bound is
uniform in the ordinate and supplies a summable zero-series majorant. -/
theorem poisson_distance_deriv_abs_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |(t ^ 2 - a ^ 2) / (a ^ 2 + t ^ 2) ^ 2| ≤ 1 / (a ^ 2 + t ^ 2) := by
  have hd : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hn : |t ^ 2 - a ^ 2| ≤ a ^ 2 + t ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg a, sq_nonneg t]
  rw [abs_div, abs_of_pos (pow_pos hd 2)]
  apply (div_le_div_iff₀ (pow_pos hd 2) hd).2
  have hm := mul_le_mul_of_nonneg_right hn hd.le
  nlinarith only [hm]

/-- For positive pole distance the absolute second derivative of the Poisson
resolvent is bounded by `6/a` times the inverse quadratic denominator. The
constant is uniform in the ordinate and controls the differentiated zero sum. -/
theorem poisson_distance_second_abs_le {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |2 * a * (a ^ 2 - 3 * t ^ 2) / (a ^ 2 + t ^ 2) ^ 3| ≤ 6 / (a * (a ^ 2 + t ^ 2)) := by
  have hd : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hn : |a ^ 2 - 3 * t ^ 2| ≤ 3 * (a ^ 2 + t ^ 2) := by
    rw [abs_le]
    constructor <;> nlinarith only [sq_nonneg a, sq_nonneg t]
  rw [abs_div, abs_mul, abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 2), abs_of_pos ha,
    abs_of_pos (pow_pos hd 3)]
  apply (div_le_div_iff₀ (pow_pos hd 3) (mul_pos ha hd)).2
  have hm :=
    mul_le_mul_of_nonneg_left hn
      (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) ha.le) (mul_nonneg ha.le hd.le))
  have ht :=
    mul_nonneg (sq_nonneg t) (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 6) (pow_nonneg hd.le 2))
  nlinarith only [hm, ht]

/-- Under individual RH, the first pole-distance derivative summed over
completed zeros is absolutely summable at every positive distance. The
pointwise derivative bound is dominated by the summable Poisson resolvent,
with the reciprocal distance as a constant factor. -/
theorem poisson_deriv_zero_summable {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ((ρ.im ^ 2 - a ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 2)) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hs :=
    (AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv
          ha).mul_left
      (a⁻¹)
  apply hs.of_norm_bounded
  intro ρ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn ρ)]
  have he :
    a⁻¹ * ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a / (a ^ 2 + ρ.im ^ 2))) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (1 / (a ^ 2 + ρ.im ^ 2)) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, one_mul]
    calc
      a⁻¹ *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
              (a * (a ^ 2 + ρ.im ^ 2)⁻¹)) =
          (a⁻¹ * a) *
            ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a ^ 2 + ρ.im ^ 2)⁻¹) :=
        by ring
      _ = _ := by rw [inv_mul_cancel₀ ha.ne', one_mul]
  rw [he]
  exact mul_le_mul_of_nonneg_left (poisson_distance_deriv_abs_le ha ρ.im) (hn ρ)

/-- Under individual RH, the second pole-distance derivative summed over
completed zeros is absolutely summable at every positive distance. Its
pointwise bound is dominated by the Poisson resolvent times `6/a^2`. -/
theorem poisson_second_zero_summable {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) {a : ℝ} (ha : 0 < a) :
    Summable
      (fun ρ : ℂ ↦
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (2 * a * (a ^ 2 - 3 * ρ.im ^ 2) / (a ^ 2 + ρ.im ^ 2) ^ 3)) := by
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hs :=
    (AnalyticNumberTheory.DirichletLFunction.summable_completed_resolvent_terms hq hRH hp hne hinv
          ha).mul_left
      (6 / a ^ 2)
  apply hs.of_norm_bounded
  intro ρ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hn ρ)]
  have he :
    (6 / a ^ 2) *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a / (a ^ 2 + ρ.im ^ 2))) =
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        (6 / (a * (a ^ 2 + ρ.im ^ 2))) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
    have hc : (a⁻¹) ^ 2 * a = a⁻¹ := by
      calc
        (a⁻¹) ^ 2 * a = a⁻¹ * (a⁻¹ * a) := by ring
        _ = _ := by rw [inv_mul_cancel₀ ha.ne', mul_one]
    calc
      _ =
          6 * (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * (a ^ 2 + ρ.im ^ 2)⁻¹ *
            ((a⁻¹) ^ 2 * a) :=
        by ring
      _ = _ := by
        rw [hc]; ring
  rw [he]
  exact mul_le_mul_of_nonneg_left (poisson_distance_second_abs_le ha ρ.im) (hn ρ)

/-- On the half-line above half a positive anchor, the first derivative of
any Poisson resolvent is bounded by four times the inverse anchor denominator.
This supplies a summable local-uniform majorant independent of the varying
pole distance. -/
theorem poisson_deriv_uniform_le {a u : ℝ} (ha : 0 < a) (hu : a / 2 ≤ u) (t : ℝ) :
    |(t ^ 2 - u ^ 2) / (u ^ 2 + t ^ 2) ^ 2| ≤ 4 / (a ^ 2 + t ^ 2) := by
  have hu0 : 0 < u := by linarith only [ha, hu]
  have hd0 : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hd1 : 0 < u ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu0) (sq_nonneg t)
  apply (poisson_distance_deriv_abs_le hu0 t).trans
  apply (div_le_div_iff₀ hd1 hd0).2
  nlinarith only [hu, ha, sq_nonneg (u - a / 2), sq_nonneg t]

/-- On the same half-line, the second Poisson derivative is bounded by
`48/a` times the inverse anchor denominator. The bound is uniform in both
the varying distance and the ordinate. -/
theorem poisson_second_uniform_le {a u : ℝ} (ha : 0 < a) (hu : a / 2 ≤ u) (t : ℝ) :
    |2 * u * (u ^ 2 - 3 * t ^ 2) / (u ^ 2 + t ^ 2) ^ 3| ≤ 48 / (a * (a ^ 2 + t ^ 2)) := by
  have hu0 : 0 < u := by linarith only [ha, hu]
  have hd0 : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  have hd1 : 0 < u ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hu0) (sq_nonneg t)
  apply (poisson_distance_second_abs_le hu0 t).trans
  apply (div_le_div_iff₀ (mul_pos hu0 hd1) (mul_pos ha hd0)).2
  have hs : a ^ 2 + t ^ 2 ≤ 4 * (u ^ 2 + t ^ 2) := by
    nlinarith only [hu, ha, sq_nonneg (u - a / 2), sq_nonneg t]
  have hm := mul_le_mul_of_nonneg_left hs ha.le
  have hn := mul_nonneg (show 0 ≤ 2 * u - a by linarith only [hu]) hd1.le
  nlinarith only [hm, hn]

end PseudoPrime.PrimeTestBounds.MillerRabin
