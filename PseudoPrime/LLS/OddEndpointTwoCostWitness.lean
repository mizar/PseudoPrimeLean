/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointBranchWitness
public import PseudoPrime.LLS.OddEndpointLogarithmicBranches

/-! # Odd-prime endpoint witnesses retaining reciprocal and logarithmic branch costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Positive-gap endpoint separation with reciprocal cost c and logarithmic
principal defect cost D. It replaces the old square-log envelope by D/sqrt x.
Inputs are totalized; the witness theorem supplies cost bounds from quadratic
values at two. This separates both arithmetic corrections from the analytic kernel. -/
noncomputable def oddEndpointTwoCostSeparation (h : ℝ) (q : ℕ) (x Y c D : ℝ) : ℝ :=
  oddEndpointCostSeparation h q x Y c + (D - (Real.log x) ^ 2) / Real.sqrt x

/-- Right-limit endpoint separation with independently chosen reciprocal and
principal defect costs c,D. Negativity with the branch upper bounds yields an
odd non-one prime. The definition is total and retains the previous signed
Gamma and conductor estimates. -/
noncomputable def oddEndpointTwoCostLimit (q : ℕ) (x Y c D : ℝ) : ℝ :=
  oddEndpointCostLimit q x Y c + (D - (Real.log x) ^ 2) / Real.sqrt x

/-- For fixed x>=1 and arbitrary q,Y,c,D, the two-cost separation tends from
the right to its stated limit. Add the gap-independent principal correction
to the established reciprocal-cost limit. No sum or integral limit is exchanged. -/
theorem tendsto_oddEndpointTwoCostSeparation_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (Y c D : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ oddEndpointTwoCostSeparation h q x Y c D) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (oddEndpointTwoCostLimit q x Y c D)) := by
  exact
    (tendsto_oddEndpointCostSeparation_right q hx Y c).add_const
      ((D - (Real.log x) ^ 2) / Real.sqrt x)

open AnalyticNumberTheory.Arithmetic in
/-- For a nonprincipal quadratic primitive associate of conductor>=2 under GRH,
64<=Y<=x, upper reciprocal and principal branch costs c,D and a negative two-cost
limit yield an odd non-one prime. Under witness nonexistence bound the reciprocal
sum and logarithmic defect, transfer the latter to the gap sum, and pass the
nonnegative separation to its right limit. Both value-at-two savings are retained. -/
theorem exists_odd_prime_inducing_ne_one_of_twoCostLimit_neg {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hC : quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ c)
    (hD : quadraticTwoLogCost x (χ.primitiveCharacter 2) ≤ D)
    (hlim : oddEndpointTwoCostLimit χ.conductor x Y c D < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ.primitiveCharacter p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1 := by
    intro p hp ho hpx
    by_contra hv
    exact hn ⟨p, hp, ho, hpx, hv⟩
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have hr :=
    reciprocalSum_re_ge_of_quadratic_two_branch χ hy2 hGRH.riemann hquad
      (fun p hp ho hpy ↦ ht p hp ho (hpy.trans hYx))
  have hlo :
    Real.log Y - (31551 / 20000 : ℝ) - c ≤
      (characterReciprocalWeightedSum Y χ.primitiveCharacter).re := by
    linarith only [hr, hC]
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

/-- For 0<q<=N,x>=1,Y>=64 and fixed c,D, the two-cost endpoint limit is monotone
in the level. The principal correction is independent of the level. This permits
one sufficient condition at the original modulus rather than at the conductor. -/
theorem oddEndpointTwoCostLimit_mono_level {q N : ℕ} {x Y c D : ℝ} (hq : 0 < q) (hqN : q ≤ N)
    (hx : 1 ≤ x) (hY : 64 ≤ Y) :
    oddEndpointTwoCostLimit q x Y c D ≤ oddEndpointTwoCostLimit N x Y c D := by
  unfold oddEndpointTwoCostLimit
  exact add_le_add (oddEndpointCostLimit_mono_level hq hqN hx hY) (le_refl _)

/-- For x>0 and any q,Y,c, using the common refined principal envelope gives a
strictly smaller separation than the former square-log principal cost. Divide
the strict scalar envelope improvement by sqrt x. This compares these conditions
at the same reciprocal cost, not all public witness bounds. -/
theorem oddEndpointTwoCostLimit_envelope_lt_costLimit (q : ℕ) {x : ℝ} (hx : 0 < x) (Y c : ℝ) :
    oddEndpointTwoCostLimit q x Y c
        ((Real.log x) ^ 2 / 2 + Real.log 2 * (Real.log x - Real.log 2)) <
      oddEndpointCostLimit q x Y c := by
  have hn :=
    div_neg_of_neg_of_pos (sub_neg.mpr (quadraticTwoLog_envelope_lt_square x))
      (Real.sqrt_pos.mpr hx)
  unfold oddEndpointTwoCostLimit
  linarith only [hn]

end PseudoPrime.LLS.PaperStatements
