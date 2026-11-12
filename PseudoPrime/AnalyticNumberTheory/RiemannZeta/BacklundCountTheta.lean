/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundCountPhase
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundTheta

/-! # Backlund zero-count inputs -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The Riemann–von Mangoldt identity for good heights and the Euler-normalized
horizontal zeta argument. This proposition specifies the remaining counting
input and does not assert its proof. -/
def EulerRiemannVonMangoldt : Prop :=
  ∀ t : ℝ,
    2 * Real.pi * Real.exp 1 ≤ t →
      (∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) →
      ∀ φ : ℝ → ℝ,
        ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) →
          (∀ x : ℝ,
            x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
              riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
                (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
                  Complex.exp ((φ x : ℂ) * Complex.I)) →
          φ (3 / 2) =
            (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
                (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im →
          AnalyticNumberTheory.RiemannZeta.positiveZeroCount t =
            1 + backlundTheta t / Real.pi + φ (1 / 2) / Real.pi

/-- The Riemann–von Mangoldt identity implies the normalized count identity
with `backlundThetaError`. The constant `7/8` follows by dividing the
`-π/8` term in the elementary Gamma phase by `π`. -/
theorem euler_phase_count_of_riemann_von_mangoldt (hV : EulerRiemannVonMangoldt) :
    EulerPhaseCountIdentity backlundThetaError := by
  intro t ht hgood φ hc hp hn
  rw [hV t ht hgood φ hc hp hn]
  dsimp only [backlundThetaError, backlundThetaMain]
  simp only [div_eq_mul_inv, mul_inv]
  have hpi : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ Real.pi_ne_zero
  nlinarith only [hpi]

/-- A Gamma phase error at most `1/(4t)` implies the weaker normalized error
bound `1/(5t)` used by the coarse count. Positivity of `t` and `π > 3`
compare the reciprocal denominators. -/
theorem theta_error_le_of_phase {t : ℝ} (ht : 0 < t)
    (h : |backlundTheta t - backlundThetaMain t| ≤ 1 / (4 * t)) :
    |backlundThetaError t| ≤ 1 / (5 * t) := by
  dsimp only [backlundThetaError]
  rw [abs_div, abs_of_pos Real.pi_pos]
  have h1 := div_le_div_of_nonneg_right h Real.pi_pos.le
  apply h1.trans
  have hp : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hden : 0 < (4 * t) * Real.pi := mul_pos (mul_pos (by norm_num only) ht) Real.pi_pos
  rw [div_div]
  apply (div_le_div_iff₀ hden (mul_pos (by norm_num only) ht)).2
  nlinarith only [ht, hp, mul_nonneg ht.le (sub_nonneg.mpr hp)]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
