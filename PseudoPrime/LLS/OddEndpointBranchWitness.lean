/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointElementaryCosts
public import PseudoPrime.LLS.OddEndpointReciprocalBranches

/-! # Odd-prime endpoint witnesses with a retained reciprocal correction cost -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Full endpoint separation with arbitrary reciprocal loss c and the logarithmic
two-power principal envelope. Inputs h,q,x,Y,c are totalized. Later theorems supply
the quadratic branch cost and positivity assumptions. This accepts improved
reciprocal input without changing the principal comparison. -/
noncomputable def oddEndpointCostSeparation (h : ℝ) (q : ℕ) (x Y c : ℝ) : ℝ :=
  reciprocalGapFullEndpointSeparation h q x Y +
    (2 + (reciprocalGapLogQuotient h x + 2) / (1 + 2 * h) / Real.sqrt x) *
      (c / (1 - 1 / Real.sqrt Y) ^ 2) +
    (Real.log x) ^ 2 / Real.sqrt x

/-- Gap-free endpoint separation with reciprocal correction c and logarithmic
two-power principal loss. Inputs q,x,Y,c are totalized. Negativity under the
quadratic branch-cost bound yields an odd non-one prime; choosing c=(4/3)log 2
removes the need to specify the value at two. -/
noncomputable def oddEndpointCostLimit (q : ℕ) (x Y c : ℝ) : ℝ :=
  reciprocalGapFullEndpointLimit q x Y +
    (2 + (Real.log x + 2) / Real.sqrt x) * (c / (1 - 1 / Real.sqrt Y) ^ 2) +
    (Real.log x) ^ 2 / Real.sqrt x

/-- For arbitrary real Y,c and natural q, subtracting c from the reciprocal lower
input adds c/(1-1/sqrt Y)^2 to the mass cap. Rearrange totalized divisions.
This generic identity separates the correction budget from the conductor term. -/
theorem reciprocalMassCap_sub_cost_eq (q : ℕ) (Y c : ℝ) :
    reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ) - c) =
      reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ)) +
        c / (1 - 1 / Real.sqrt Y) ^ 2 := by
  unfold reciprocalGapReciprocalMassCap
  simp only [div_eq_mul_inv]
  ring

/-- For x>=1 and arbitrary q,Y,c, the cost-parametrized separation tends from the
right to its displayed limit. Use the full endpoint limit and the rational
coefficient limit. Neither an arithmetic sum nor a zero sum is interchanged. -/
theorem tendsto_oddEndpointCostSeparation_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (Y c : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ oddEndpointCostSeparation h q x Y c) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (oddEndpointCostLimit q x Y c)) := by
  have hi : Filter.Tendsto (fun h : ℝ ↦ h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds
  have hd2 : Filter.Tendsto (fun h : ℝ ↦ 1 + 2 * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds.add (hi.const_mul 2) :
        Filter.Tendsto (fun h : ℝ ↦ 1 + 2 * h) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 + 2 * 0)))
  have hc :
    Filter.Tendsto (fun h : ℝ ↦ (reciprocalGapLogQuotient h x + 2) / (1 + 2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.log x + 2)) := by
    simpa only [Pi.div_def, div_one] using
      (((tendsto_reciprocalGapLogQuotient_right hx).add_const 2).div hd2
        (by norm_num only : (1 : ℝ) ≠ 0))
  dsimp only [oddEndpointCostSeparation, oddEndpointCostLimit]
  exact
    ((tendsto_reciprocalGapFullEndpointSeparation_right q hx Y).add
          (((hc.div_const (Real.sqrt x)).const_add 2).mul_const
            (c / (1 - 1 / Real.sqrt Y) ^ 2))).add_const
      _

open AnalyticNumberTheory.Arithmetic in
/-- For an original character with nonprincipal quadratic primitive associate of
conductor>=2 under GRH, 64<=Y<=x, a branch-cost upper bound c and negative limit
give an odd non-one prime for the primitive associate. Under nonexistence apply
the refined reciprocal branch input and the analytic odd-prime principal lower
bound. Pass the nonnegative separation to its right limit for a contradiction. -/
theorem exists_odd_prime_inducing_ne_one_of_costLimit_neg {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hC : quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ c)
    (hlim : oddEndpointCostLimit χ.conductor x Y c < 0) :
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
  have hnonneg :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 ≤ oddEndpointCostSeparation h χ.conductor x Y c := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro h hh
    have hU :=
      reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH χ.primitiveCharacter_isPrimitive hne
        hi hx.le hm
    have hL :=
      reciprocalGapSum_re_ge_of_odd_prime_trivial χ.primitiveCharacter hh hx hGRH.riemann ht
    have hl := (oddEndpoint_two_part_costs_le (zero_lt_one.trans hx)).2
    have hc :
      2 * commonFactorLogWeightedSum x 2 / Real.sqrt x ≤ (Real.log x) ^ 2 / Real.sqrt x := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
      linarith only [hl]
    let M := reciprocalGapReciprocalMassCap χ.conductor Y (Real.log Y - (31551 / 20000 : ℝ))
    let C := c / (1 - 1 / Real.sqrt Y) ^ 2
    let A :=
      (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
        (Real.sqrt x * (1 + h * Real.log x))
    have he :
      oddEndpointCostSeparation h χ.conductor x Y c =
        2 * (M + C) + reciprocalGapEndpointMassBudget h χ.conductor x (M + C) +
              reciprocalGapSignedGammaBudget h x -
            A +
          (Real.log x) ^ 2 / Real.sqrt x := by
      dsimp only [oddEndpointCostSeparation, reciprocalGapFullEndpointSeparation,
        reciprocalGapEndpointMassBudget, M, C, A]
      ring
    rw [he]
    change
      (reciprocalGapCharacterSum h χ.primitiveCharacter x).re ≤
        2 * (M + C) + reciprocalGapEndpointMassBudget h χ.conductor x (M + C) +
          reciprocalGapSignedGammaBudget h x at hU
    change
      A - 2 * commonFactorLogWeightedSum x 2 / Real.sqrt x ≤
        (reciprocalGapCharacterSum h χ.primitiveCharacter x).re at hL
    linarith only [hU, hL, hc]
  have hz : 0 ≤ oddEndpointCostLimit χ.conductor x Y c :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_oddEndpointCostSeparation_right χ.conductor hx.le Y c) hnonneg
  exact (not_lt_of_ge hz) hlim

/-- For 0<q<=N,x>=1,Y>=64 and any cost c, the cost endpoint limit is monotone in
the level. Only the full endpoint part depends on the level. This allows the
canonical conductor to be replaced by the original modulus. -/
theorem oddEndpointCostLimit_mono_level {q N : ℕ} {x Y c : ℝ} (hq : 0 < q) (hqN : q ≤ N)
    (hx : 1 ≤ x) (hY : 64 ≤ Y) : oddEndpointCostLimit q x Y c ≤ oddEndpointCostLimit N x Y c := by
  unfold oddEndpointCostLimit
  exact add_le_add (add_le_add (fullEndpointLimit_mono_level hq hqN hx hY) (le_refl _)) (le_refl _)

/-- For x>=1,Y>=64, the endpoint limit with cost (4/3)log 2 is strictly smaller
than the previous elementary limit with cost 2log 2. Factor their difference and
prove its positive factors. This compares those two sufficient conditions only. -/
theorem oddEndpointCostLimit_four_thirds_lt_elementary (q : ℕ) {x Y : ℝ} (hx : 1 ≤ x)
    (hY : 64 ≤ Y) :
    oddEndpointCostLimit q x Y ((4 / 3 : ℝ) * Real.log 2) < oddEndpointElementaryLimit q x Y := by
  have hy1 : 1 < Y := by linarith only [hY]
  have hs : 1 < Real.sqrt Y := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hy1
  have hd : 0 < 1 - 1 / Real.sqrt Y := sub_pos.mpr ((div_lt_one (zero_lt_one.trans hs)).mpr hs)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hk : 0 < 2 + (Real.log x + 2) / Real.sqrt x :=
    add_pos_of_pos_of_nonneg (by norm_num only)
      (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x))
  have he :
    oddEndpointElementaryLimit q x Y - oddEndpointCostLimit q x Y ((4 / 3 : ℝ) * Real.log 2) =
      (2 + (Real.log x + 2) / Real.sqrt x) *
        (((2 / 3 : ℝ) * Real.log 2) / (1 - 1 / Real.sqrt Y) ^ 2) := by
    unfold oddEndpointElementaryLimit oddEndpointCostLimit
    simp only [div_eq_mul_inv]
    ring
  apply sub_pos.mp
  rw [he]
  exact mul_pos hk (div_pos (mul_pos (by norm_num only) hl) (sq_pos_of_pos hd))

end PseudoPrime.LLS.PaperStatements
