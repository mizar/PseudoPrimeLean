/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness

/-!
# Xi zeros and logarithmic derivatives after translation

Translation by one half preserves finite multiplicities and compact zero finiteness.
These identities support shifted Mellin residue contours without requiring RH.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- Translation by one half preserves the analytic order of xi at every point.
The translation has derivative one, so the analytic-order composition theorem applies.
This identifies multiplicities in shifted Mellin contours. -/
theorem shifted_analyticOrderAt (s : ℂ) :
    analyticOrderAt (fun z : ℂ => riemannXi (z + 1 / 2)) s =
      analyticOrderAt riemannXi (s + 1 / 2) := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := analyticAt_id.add analyticAt_const
  have hd : deriv (fun z : ℂ => z + 1 / 2) s ≠ 0 :=
    (((hasDerivAt_id s).add_const (1 / 2)).deriv).trans_ne one_ne_zero
  exact analyticOrderAt_comp_of_deriv_ne_zero (f := riemannXi) ha hd

/-- The shifted xi function has finite analytic order at every complex point.
Translate to the existing finite-order theorem for the entire nonzero xi function.
This excludes infinite multiplicities from shifted zero ledgers. -/
theorem shifted_analyticOrderAt_ne_top (s : ℂ) :
    analyticOrderAt (fun z : ℂ => riemannXi (z + 1 / 2)) s ≠ ⊤ := by
  rw [shifted_analyticOrderAt]
  exact riemannXi_analyticOrderAt_ne_top _

/-- On any compact complex set, xi shifted by one half has finitely many zeros.
Entirety and finite analytic order identify zeros with the support of its meromorphic
divisor, whose support is finite on compact sets. This supplies shifted contour ledgers. -/
theorem finite_shifted_zeros {U : Set ℂ} (hU : IsCompact U) :
    (U ∩ (fun z : ℂ => riemannXi (z + 1 / 2)) ⁻¹' {0}).Finite := by
  let F := fun z : ℂ => riemannXi (z + 1 / 2)
  have hF : AnalyticOnNhd ℂ F U := fun z _ =>
    (differentiable_riemannXi.analyticAt _).comp (analyticAt_id.add analyticAt_const)
  have hn := hF.meromorphicNFOn
  rw [hn.zero_set_eq_divisor_support fun u => ?_]
  · exact (MeromorphicOn.divisor F U).finiteSupport hU
  · rw [(hF u u.property).meromorphicOrderAt_eq]
    exact fun ht => shifted_analyticOrderAt_ne_top u (ENat.map_eq_top_iff.mp ht)

/-- The logarithmic derivative of xi shifted by one half equals the unshifted
logarithmic derivative at the translated point. The chain rule and unit translation
derivative prove the identity, including totalized values at zeros. This connects
shifted local residues with the xi contour integrand. -/
theorem logDeriv_shifted (s : ℂ) :
    logDeriv (fun z : ℂ => riemannXi (z + 1 / 2)) s = logDeriv riemannXi (s + 1 / 2) := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) s := differentiableAt_id.add_const _
  have he := logDeriv_comp (differentiable_riemannXi _) hd
  simpa only [Function.comp_def, deriv_add_const, deriv_id'', mul_one] using he

end PseudoPrime.AnalyticNumberTheory.RiemannXi
