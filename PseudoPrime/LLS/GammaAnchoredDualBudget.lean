/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaAnchoredRamifiedSupport
public import PseudoPrime.LLS.GammaScaleJointBudget

/-! # Actual signed dual budgets on the smaller anchored support -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: any logarithmic level and x >= 1. Claim: the actual signed dual
budget is bounded using only odd primes through the anchored support.
Apply tail vanishing to the original support. Role: reduce the numerical
obligation without changing the underlying arithmetic budget. -/
theorem gammaSignedDual_le_anchorSupport {L x : ℝ} (hx : 1 ≤ x) :
    gammaScaleSignedDualBudget L x ≤
      gammaRamifiedDualParameter x * L +
        ∑ p ∈ gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x)),
          Real.log p *
            max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  have h :=
    gamma_anchored_signed_excess_le_certificate (gammaRamifiedDualPrimeSet x)
      (fun p hp ↦ ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩)
      (a := 160) (B := 13 / 25) (θ := 5 / 4) (by norm_num only) hx
      (fun p hp ha ↦ Analysis.gamma_euler_anchor160_reciprocal hp ha) (gamma_anchor160_cutoff_le hx)
  rw [gamma_ramified_theta_parameter_five_fourths] at h
  exact add_le_add le_rfl h

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: any logarithmic level and x >= 1. Claim: replacing the original
prime support by the anchored support leaves the exact dual budget unchanged.
Use tail vanishing in both directions. Role: shrink the finite obligation
without introducing any loss in the numerical upper bound. -/
theorem gammaSignedDual_eq_anchor160Support {L x : ℝ} (hx : 1 ≤ x) :
    gammaScaleSignedDualBudget L x =
      gammaRamifiedDualParameter x * L +
        ∑ p ∈ gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x)),
          Real.log p *
            max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0 := by
  apply le_antisymm (gammaSignedDual_le_anchorSupport hx)
  have h :=
    gamma_ramified_signed_variable_excess_le_finite
      (gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x)))
      (fun p hp ↦ ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1⟩)
      hx
  exact add_le_add le_rfl h

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: x >= 1 and an upper cap E on the anchored signed excess sum.
Claim: the full dual budget is at most delta(x)*L+E. Add the unchanged
linear term. Role: feed compact local bounds to quadratic witnesses. -/
theorem gamma_signed_dual_budget_le_of_anchor {L x E : ℝ} (hx : 1 ≤ x)
    (hrows :
      (∑ p ∈ gammaRamifiedCertificatePrimeSet (max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x)),
          Real.log p * max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedDualParameter x) 0) ≤
        E) :
    gammaScaleSignedDualBudget L x ≤ gammaRamifiedDualParameter x * L + E := by
  exact (gammaSignedDual_le_anchorSupport hx).trans (add_le_add le_rfl hrows)

end PseudoPrime.LLS
