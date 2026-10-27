/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TaperedTwoReciprocalCost

/-! # Odd quadratic witnesses retaining finite reciprocal taper savings -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For quadratic nonprincipal primitive GRH data and 64<=Y<=x, bounds on the
exact two-adic reciprocal correction and logarithmic branch cost with negative
endpoint limit yield an odd non-one prime. Use the exact reciprocal lower input,
then pass the established nonnegative gap comparison to its endpoint limit. -/
theorem exists_odd_prime_inducing_ne_one_of_exact_two_cost_limit {N : ℕ}
    (χ : DirichletCharacter ℂ N) [NeZero χ.conductor] (hq : 2 ≤ χ.conductor)
    (hne : χ.primitiveCharacter ≠ 1) (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hC : twoAdicReciprocalCorrection Y χ ≤ c)
    (hD : quadraticTwoLogCost x (χ.primitiveCharacter 2) ≤ D)
    (hlim : oddEndpointTwoCostLimit χ.conductor x Y c D < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ.primitiveCharacter p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1 := by
    intro p hp ho hpx
    by_contra hv
    exact hn ⟨p, hp, ho, hpx, hv⟩
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have hlo :=
    reciprocalSum_re_ge_of_twoAdicCorrection_le χ hy2 hGRH.riemann
      (fun p hp ho hpy ↦ ht p hp ho (hpy.trans hYx)) hC
  have hi : χ.primitiveCharacter⁻¹ ≠ 1 := fun h ↦ hne (inv_eq_one.mp h)
  have hm :=
    reciprocalGap_mass_le_reciprocal_cap hq hGRH χ.primitiveCharacter_isPrimitive hne hi hY hlo
  rw [reciprocalMassCap_sub_cost_eq] at hm
  have hx4 : 4 ≤ x := le_trans (by linarith only [hY] : 4 ≤ Y) hYx
  have hlog := (log_defect_le_quadratic_two_branch χ hx4 hquad ht).trans hD
  have hnonneg :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 ≤ oddEndpointTwoCostSeparation h χ.conductor x Y c D := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro h hh
    have hU :=
      reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH χ.primitiveCharacter_isPrimitive hne
        hi hx.le hm
    have hL := reciprocalGapSum_re_ge_of_log_defect_le χ.primitiveCharacter hh hx hGRH.riemann hlog
    let M := reciprocalGapReciprocalMassCap χ.conductor Y (Real.log Y - (31551 / 20000 : ℝ))
    let C := c / (1 - 1 / Real.sqrt Y) ^ 2
    let A :=
      (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
        (Real.sqrt x * (1 + h * Real.log x))
    have he :
      oddEndpointTwoCostSeparation h χ.conductor x Y c D =
        2 * (M + C) + reciprocalGapEndpointMassBudget h χ.conductor x (M + C) +
              reciprocalGapSignedGammaBudget h x -
            A +
          D / Real.sqrt x := by
      dsimp only [oddEndpointTwoCostSeparation, oddEndpointCostSeparation,
        reciprocalGapFullEndpointSeparation, reciprocalGapEndpointMassBudget, M, C, A]
      ring
    rw [he]
    change
      (reciprocalGapCharacterSum h χ.primitiveCharacter x).re ≤
        2 * (M + C) + reciprocalGapEndpointMassBudget h χ.conductor x (M + C) +
          reciprocalGapSignedGammaBudget h x at hU
    change A - D / Real.sqrt x ≤ (reciprocalGapCharacterSum h χ.primitiveCharacter x).re at hL
    linarith only [hU, hL]
  have hz : 0 ≤ oddEndpointTwoCostLimit χ.conductor x Y c D :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_oddEndpointTwoCostSeparation_right χ.conductor hx.le Y c D) hnonneg
  exact (not_lt_of_ge hz) hlim

/-- Under quadratic nonprincipal primitive GRH data and 64<=Y<=x, the tapered
reciprocal cost and a logarithmic branch bound give an odd non-one prime whenever
the refined endpoint limit is negative. Insert the proved exact correction bound.
This exposes the finite-cutoff improvement to witness consumers. -/
theorem exists_odd_prime_inducing_ne_one_of_tapered_limit {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hD : quadraticTwoLogCost x (χ.primitiveCharacter 2) ≤ D)
    (hlim :
      oddEndpointTwoCostLimit χ.conductor x Y (taperedTwoReciprocalCost Y (χ.primitiveCharacter 2))
          D <
        0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ.primitiveCharacter p ≠ 1 := by
  exact
    exists_odd_prime_inducing_ne_one_of_exact_two_cost_limit χ hq hne hquad hGRH hx hY hYx
      (twoAdicReciprocalCorrection_le_tapered χ Y hquad) hD hlim

end PseudoPrime.LLS.PaperStatements
