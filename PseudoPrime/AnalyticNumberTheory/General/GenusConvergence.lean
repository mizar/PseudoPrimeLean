/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.EntireZeroMass

/-!
# Absolute convergence of genus-one zero series

Use the finite multiplicity support in compact disks and quadratic tail decay
to pass from Jensen's regularized zero mass to the logarithmic zero expansion.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Outside the disk of radius max(1, 2*norm s), the genus-one term is bounded
by 4*norm s/(1+norm rho squared). The triangle inequality separates s from rho;
combining the reciprocal fractions gives quadratic decay. This estimate needs
no restriction on the real part of rho and controls the tail of the zero series. -/
theorem norm_genusTerm_le_regularWeight {s ρ : ℂ} (h1 : 1 ≤ ‖ρ‖) (h2 : 2 * ‖s‖ ≤ ‖ρ‖) :
    ‖1 / (s - ρ) + 1 / ρ‖ ≤ 4 * ‖s‖ / (1 + ‖ρ‖ ^ 2) := by
  have hp : 0 < ‖ρ‖ := lt_of_lt_of_le zero_lt_one h1
  have hd : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have hn := norm_sub_le s (s - ρ)
    rw [sub_sub_cancel] at hn
    linarith only [hn, h2]
  have hd0 : 0 < ‖s - ρ‖ := (half_pos hp).trans_le hd
  rw [div_add_div 1 1 (norm_pos_iff.mp hd0) (norm_pos_iff.mp hp)]
  simp only [one_mul, mul_one, add_sub_cancel]
  rw [norm_div, norm_mul,
    div_le_div_iff₀ (mul_pos hd0 hp) (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg ‖ρ‖))]
  have hsq : 1 + ‖ρ‖ ^ 2 ≤ 2 * ‖ρ‖ ^ 2 := by nlinarith only [h1, sq_nonneg (‖ρ‖ - 1)]
  have hm := mul_le_mul_of_nonneg_left hd hp.le
  have hprod := mul_le_mul_of_nonneg_left hm (norm_nonneg s)
  have hprod2 := mul_le_mul_of_nonneg_left hsq (norm_nonneg s)
  nlinarith only [hprod, hprod2]

/-- For an entire F, summability of its regularized multiplicity mass implies
absolute convergence of its genus-one series at every s. Remove the finitely
many nonzero multiplicities in a compact disk and dominate the remaining terms
by the regularized mass. Restoring finitely many terms preserves convergence.
This also applies at zeros, with Lean's total reciprocal convention. -/
theorem summable_genusTerms_of_regularZeroWeight {F : ℂ → ℂ} (hF : Differentiable ℂ F) {s : ℂ}
    (hm : Summable (regularZeroWeight F)) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
  classical
  let R : ℝ := max 1 (2 * ‖s‖)
  let D := MeromorphicOn.divisor F (Metric.closedBall (0 : ℂ) R)
  let E := Function.support D
  have hE : E.Finite := D.finiteSupport (isCompact_closedBall (x := (0 : ℂ)) (r := R))
  let T : ℂ → ℂ := fun ρ ↦ if ρ ∈ E then 0 else (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)
  have hT : Summable T := by
    apply Summable.of_norm_bounded (hm.mul_left (4 * ‖s‖))
    intro ρ
    by_cases hρ : ρ ∈ E
    · simp only [T, ite_eq_left hρ, norm_zero]
      exact
        mul_nonneg (mul_nonneg (by norm_num only) (norm_nonneg s)) (regularZeroWeight_nonneg F ρ)
    · simp only [T, ite_eq_right hρ, norm_mul, norm_natCast]
      by_cases hb : ‖ρ‖ ≤ R
      · have ho : analyticOrderNatAt F ρ = 0 := by
          have hz : D ρ = 0 := by simpa only [E, Function.mem_support, not_not] using hρ
          rw [divisor_closedBall_eq_order hF
              (by simpa only [Metric.mem_closedBall, dist_zero_right] using hb)] at hz
          exact_mod_cast hz
        simp only [ho, Nat.cast_zero, zero_mul, regularZeroWeight, zero_div, mul_zero, le_refl]
      · have hr : R ≤ ‖ρ‖ := (lt_of_not_ge hb).le
        have hg :=
          norm_genusTerm_le_regularWeight ((le_max_left _ _).trans hr) ((le_max_right _ _).trans hr)
        have hv :=
          mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (analyticOrderNatAt F ρ) : (0 : ℝ) ≤ _)
        exact
          hv.trans_eq
            (by
              unfold regularZeroWeight
              ring)
  apply hT.congr_cofinite
  filter_upwards [hE.compl_mem_cofinite] with ρ hρ
  simp only [T, ite_eq_right hρ]

/-- An entire F nonzero at zero with exponential growth of exponent below two
has an absolutely convergent genus-one series at every complex s.
Jensen's multiplicity estimate gives regularized zero mass; the preceding tail
comparison then removes the separate convergence assumption from Hadamard
logarithmic derivative identities. No Riemann hypothesis is required. -/
theorem summable_genusTerms_of_entireGrowth {F : ℂ → ℂ} (hF : Differentiable ℂ F) (h0 : F 0 ≠ 0)
    {C r : ℝ} (hC : 0 < C) (hr0 : 0 ≤ r) (hr2 : r < 2)
    (hg : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (‖z‖ + 1) ^ r)) (s : ℂ) :
    Summable (fun ρ : ℂ ↦ (analyticOrderNatAt F ρ : ℂ) * (1 / (s - ρ) + 1 / ρ)) := by
  exact summable_genusTerms_of_regularZeroWeight hF (summable_regularZeroWeight hF h0 hC hr0 hr2 hg)

end PseudoPrime.AnalyticNumberTheory.General
