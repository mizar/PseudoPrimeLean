/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareSchur
public import PseudoPrime.AnalyticNumberTheory.General.PoissonZeroMass

/-!
# Mean squares of actual multiplicity-weighted zero sums

The reflected logarithmic derivative controls every Gram row and hence the energy
of finite height prefixes. Neither RH nor pair correlation is required for the
general entire-completion statements.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A nonnegative multiplicity times the Gram kernel is at most nine times its
Poisson profile with denominator nine. This matches the existing zero-mass theorem. -/
theorem multiplicity_gram_le_poisson {m : ℝ} (hm : 0 ≤ m) (x : ℝ) :
    m * PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel x ≤ 9 * (m / (9 + x ^ 2)) := by
  have h :=
    mul_le_mul_of_nonneg_left (PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel_le_poisson x)
      hm
  convert h using 1
  ring

/-- For an entire order-one completion with conjugate functional equation, right
half-plane nonvanishing, and nonzero value at zero, every finite multiplicity-weighted
Gram row is at most nine times the real logarithmic derivative at 3+iT.
Compare with the summable actual Poisson zero mass; no zero-spacing hypothesis is used. -/
theorem finite_zero_gram_row_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (S : Finset ℂ) (T : ℝ) :
    ∑ ρ ∈ S,
        (analyticOrderNatAt F ρ : ℝ) *
          PseudoPrime.Analysis.ExponentialMeanSquare.gramKernel (T - ρ.im) ≤
      9 * (logDeriv F (((3 : ℝ) : ℂ) + T * Complex.I)).re := by
  have hp := poissonZeroMass_bound_of_orderAtMostOne hε hfe hright hF h0 horder T
  have hs :=
    Summable.sum_le_tsum S
      (fun ρ hρ ↦
        div_nonneg (Nat.cast_nonneg (analyticOrderNatAt F ρ))
          (by nlinarith only [sq_nonneg (T - ρ.im)] : 0 ≤ 9 + (T - ρ.im) ^ 2))
      hp.1
  have hc :=
    Finset.sum_le_sum (s := S)
      (fun ρ hρ ↦
        multiplicity_gram_le_poisson (Nat.cast_nonneg (analyticOrderNatAt F ρ)) (T - ρ.im))
  rw [← Finset.mul_sum] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left (hs.trans hp.2) (by norm_num only))

/-- A uniform upper bound R for the actual reflected logarithmic derivative at the
finite zero heights gives energy at most 9R times the multiplicity-weighted coefficient
l2 mass. Supply the actual Gram rows to Schur, without assuming an energy estimate. -/
theorem finite_zero_energy_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (S : Finset ℂ)
    (a : ℂ → ℂ) {R : ℝ} (hR : ∀ ρ ∈ S, (logDeriv F (((3 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ R) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * a ρ)) ≤
      (9 * R) * ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖a ρ‖ ^ 2 := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.energy_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt F ρ : ℝ)) a (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  exact
    (finite_zero_gram_row_le hε hfe hright hF h0 horder S ρ.im).trans
      (mul_le_mul_of_nonneg_left (hR ρ hρ) (by norm_num only))

/-- The same logarithmic-derivative bound controls every actual finite height prefix.
The coefficient cutoff is handled by the proved Schur prefix theorem, rather than
an unjustified monotonicity assertion for zero-sum energies. -/
theorem finite_zero_prefix_energy_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (S : Finset ℂ)
    (a : ℂ → ℂ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ ρ ∈ S, (logDeriv F (((3 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ R) (t : ℝ) :
    PseudoPrime.Analysis.ExponentialMeanSquare.energy
        (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
          (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
            (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * a ρ) t)) ≤
      (9 * R) * ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖a ρ‖ ^ 2 := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.energy_prefix_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt F ρ : ℝ)) a (mul_nonneg (by norm_num only) hR0)
      (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  exact
    (finite_zero_gram_row_le hε hfe hright hF h0 horder S ρ.im).trans
      (mul_le_mul_of_nonneg_left (hR ρ hρ) (by norm_num only))

/-- The same actual reflected rows supply the Abel block point bound for zero-height
prefixes, with no independent prefix-energy or derivative-energy assumptions. -/
theorem finite_zero_block_point_le {F : ℂ → ℂ} {ε : ℂ} (hε : ε ≠ 0)
    (hfe : ∀ z, F z = ε * star (F (1 - star z))) (hright : ∀ s, 1 < s.re → F s ≠ 0)
    (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0) (horder : HasOrderAtMostOne F) (S : Finset ℂ)
    (a : ℂ → ℂ) {U T R : ℝ} (hU : 0 ≤ U) (hUT : U ≤ T) (hR0 : 0 ≤ R)
    (hR : ∀ ρ ∈ S, (logDeriv F (((3 : ℝ) : ℂ) + ρ.im * Complex.I)).re ≤ R) :
    ‖PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * a ρ) T)
              0 -
            PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum S Complex.im
              (PseudoPrime.Analysis.ExponentialMeanSquare.heightCoefficients Complex.im
                (fun ρ ↦ ((analyticOrderNatAt F ρ : ℝ) : ℂ) * a ρ) U)
              0‖ ^
        2 ≤
      4 * (1 + 2 * T - U) * ((9 * R) * ∑ ρ ∈ S, (analyticOrderNatAt F ρ : ℝ) * ‖a ρ‖ ^ 2) := by
  apply
    PseudoPrime.Analysis.ExponentialMeanSquare.block_point_le_weighted_rows S Complex.im
      (fun ρ ↦ (analyticOrderNatAt F ρ : ℝ)) a hU hUT (mul_nonneg (by norm_num only) hR0)
      (fun ρ hρ ↦ Nat.cast_nonneg _)
  intro ρ hρ
  exact
    (finite_zero_gram_row_le hε hfe hright hF h0 horder S ρ.im).trans
      (mul_le_mul_of_nonneg_left (hR ρ hρ) (by norm_num only))

end PseudoPrime.AnalyticNumberTheory.General
