/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZero644
public import PseudoPrime.LLS.PaperStatements.MellinKernelZeta
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalPoissonRH

/-! # The xi Poisson identity for the section 122 zero mass -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply the section 122 sixth-pole operator to the real shift of a
complex function. The evaluation uses its value and first two real derivatives. -/
@[expose]
noncomputable def quarterXiOperator (f : ℂ → ℂ) : ℝ :=
  let F : ℝ → ℝ := fun u ↦ (f (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re
  3 * F (107 / 100) - (321 / 100 : ℝ) * deriv F (107 / 100) +
    (11449 / 10000 : ℝ) * deriv (deriv F) (107 / 100)

/-- The real xi logarithmic derivative at horizontal distance u from the
critical line. Its first two derivatives enter the sixth-pole formula. -/
private noncomputable def quarterXiLog (u : ℝ) : ℝ :=
  (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi (((1 / 2 : ℝ) + u : ℝ) : ℂ)).re

private theorem xi_hasSum (hRH : RiemannHypothesis) {u : ℝ} (hu : 0 < u) :
    HasSum
      (fun ρ : ℂ ↦
        (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℝ) *
          (u / (u ^ 2 + ρ.im ^ 2)))
      (quarterXiLog u) := by
  have h : 1 / 2 < (((1 / 2 : ℝ) + u : ℝ) : ℂ).re := by
    rw [Complex.ofReal_re]
    exact lt_add_of_pos_right _ hu
  simpa only [quarterXiLog, Complex.ofReal_re, Complex.ofReal_im, add_sub_cancel_left, zero_sub,
    neg_sq] using AnalyticNumberTheory.RiemannXi.hasSum_logDeriv_poisson hRH h

private theorem xi_deriv (hRH : RiemannHypothesis) {u : ℝ} (hu : 0 < u) :
    HasDerivAt quarterXiLog
      (∑' ρ : ℂ,
        (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℝ) *
          ((ρ.im ^ 2 - u ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 2))
      u := by
  apply
    (hasDerivAt_poisson_sum hu (fun _ ↦ Nat.cast_nonneg _)
        (xi_hasSum hRH hu).summable).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact (xi_hasSum hRH hv).tsum_eq.symm

private theorem xi_deriv_two (hRH : RiemannHypothesis) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (deriv quarterXiLog)
      (∑' ρ : ℂ,
        (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℝ) *
          (2 * u * (u ^ 2 - 3 * ρ.im ^ 2) / (u ^ 2 + ρ.im ^ 2) ^ 3))
      u := by
  apply
    (hasDerivAt_poisson_deriv_sum hu (fun _ ↦ Nat.cast_nonneg _)
        (xi_hasSum hRH hu).summable).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact (xi_deriv hRH hv).deriv

private theorem xi_mass_eq (hRH : RiemannHypothesis) {u : ℝ} (hu : 0 < u) :
    (∑' ρ : ℂ,
        (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℝ) *
          (8 * u ^ 5 / (u ^ 2 + ρ.im ^ 2) ^ 3)) =
      3 * quarterXiLog u - 3 * u * deriv quarterXiLog u + u ^ 2 * deriv (deriv quarterXiLog) u := by
  rw [(xi_deriv hRH hu).deriv, (xi_deriv_two hRH hu).deriv, ← (xi_hasSum hRH hu).tsum_eq]
  exact sixth_pole_weighted_identity hu (fun _ ↦ Nat.cast_nonneg _) (xi_hasSum hRH hu).summable

/-- Under RH, eight times the section 122 zeta zero mass equals the
second-order Poisson operator on the real xi logarithmic derivative.
The multiplicity-weighted identity and the kernel norm identify the mass. -/
theorem quarter_xi_poisson_644 (hRH : RiemannHypothesis) :
    8 * (∑' ρ, ‖quarterKernel644.zetaKernelZeroTerm ρ‖) =
      quarterXiOperator (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi) := by
  change
    _ =
      3 * quarterXiLog (107 / 100) - (321 / 100 : ℝ) * deriv quarterXiLog (107 / 100) +
        (11449 / 10000 : ℝ) * deriv (deriv quarterXiLog) (107 / 100)
  have h := xi_mass_eq hRH (u := 107 / 100) (by norm_num only)
  have hD :
    3 * quarterXiLog (107 / 100) - 3 * (107 / 100 : ℝ) * deriv quarterXiLog (107 / 100) +
        (107 / 100 : ℝ) ^ 2 * deriv (deriv quarterXiLog) (107 / 100) =
      3 * quarterXiLog (107 / 100) - (321 / 100 : ℝ) * deriv quarterXiLog (107 / 100) +
        (11449 / 10000 : ℝ) * deriv (deriv quarterXiLog) (107 / 100) := by
    ring
  rw [← hD, ← h, ← tsum_mul_left]
  let F := fun ρ : ℂ ↦
    (analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ : ℝ) *
      (8 * (107 / 100 : ℝ) ^ 5 / ((107 / 100 : ℝ) ^ 2 + ρ.im ^ 2) ^ 3)
  have hs : Function.support F ⊆ {ρ | AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0} := by
    intro ρ hρ
    by_contra hn
    have ho : analyticOrderNatAt AnalyticNumberTheory.RiemannXi.riemannXi ρ = 0 := by
      rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hn), ENat.toNat_zero]
    exact hρ (by simp only [F, ho, Nat.cast_zero, zero_mul])
  change (∑' ρ, 8 * ‖quarterKernel644.zetaKernelZeroTerm ρ‖) = ∑' ρ, F ρ
  rw [← tsum_subtype_eq_of_support_subset hs]
  apply tsum_congr
  intro ρ
  rw [LLS.PaperStatements.MellinKernel.zetaKernelZeroTerm, norm_mul, Complex.norm_natCast,
    quarter_zero_norm_644]
  unfold F AnalyticNumberTheory.RiemannXi.riemannXiZeroMultiplicity
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
