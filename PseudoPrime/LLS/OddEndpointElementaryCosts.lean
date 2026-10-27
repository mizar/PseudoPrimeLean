/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointWitness
public import PseudoPrime.LLS.ReciprocalGapFullEndpointMonotone

/-! # Elementary two-power costs and conductor monotonicity for odd witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For positive x, the reciprocal two-part sum is at most log 2, and the
logarithmic two-part sum is at most (log x)^2/2. Specialize the general common-factor
bounds using the prime-factor support {2}. These are analytic bounds for every cutoff. -/
theorem oddEndpoint_two_part_costs_le {x : ℝ} (hx : 0 < x) :
    commonFactorReciprocalWeightedSum x 2 ≤ Real.log 2 ∧
      commonFactorLogWeightedSum x 2 ≤ (1 / 2 : ℝ) * (Real.log x) ^ 2 := by
  have he : (2 : ℕ).primeFactors = {2} := by
    simpa only [pow_one] using
      Nat.primeFactors_prime_pow (by norm_num only : (1 : ℕ) ≠ 0) Nat.prime_two
  have hr := commonFactorReciprocalWeightedSum_le (by norm_num only : (2 : ℕ) ≠ 0) hx
  have hl := commonFactorLogWeightedSum_le (by norm_num only : (2 : ℕ) ≠ 0) hx
  norm_num only [primeFactorLogSum, he, Finset.sum_singleton, Finset.card_singleton, div_one,
    mul_one] at hr hl
  exact ⟨hr, hl⟩

/-- Elementary odd-prime endpoint limit: the full-prime limit plus mass correction
bounded using log 2 and principal loss bounded using (log x)^2. Inputs q,x,Y are
totalized; negativity with 64<=Y<=x produces a witness. No prime-factor sum or
finite support occurs in this explicit logarithmic criterion. -/
noncomputable def oddEndpointElementaryLimit (q : ℕ) (x Y : ℝ) : ℝ :=
  reciprocalGapFullEndpointLimit q x Y +
    (2 + (Real.log x + 2) / Real.sqrt x) * (2 * Real.log 2 / (1 - 1 / Real.sqrt Y) ^ 2) +
    (Real.log x) ^ 2 / Real.sqrt x

/-- For x>=1 and Y>0, the exact odd endpoint limit is at most the elementary
limit. Bound its reciprocal mass correction and logarithmic principal loss with
the two-part estimates; their scalar coefficients are nonnegative. -/
theorem oddEndpointLimit_le_elementary (q : ℕ) {x Y : ℝ} (hx : 1 ≤ x) (hY : 0 < Y) :
    oddEndpointLimit q x Y ≤ oddEndpointElementaryLimit q x Y := by
  have hr := (oddEndpoint_two_part_costs_le hY).1
  have hl := (oddEndpoint_two_part_costs_le (zero_lt_one.trans_le hx)).2
  have hm : oddEndpointMassCorrection Y ≤ 2 * Real.log 2 / (1 - 1 / Real.sqrt Y) ^ 2 := by
    unfold oddEndpointMassCorrection
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left hr (by norm_num only)
  have hk : 0 ≤ 2 + (Real.log x + 2) / Real.sqrt x :=
    add_nonneg (by norm_num only)
      (div_nonneg (by linarith only [Real.log_nonneg hx]) (Real.sqrt_nonneg x))
  have he :
    2 * AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x 2 / Real.sqrt x ≤
      (Real.log x) ^ 2 / Real.sqrt x := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg x)
    linarith only [hl]
  unfold oddEndpointLimit oddEndpointElementaryLimit
  exact add_le_add (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hm hk)) he

/-- For primitive nonprincipal GRH data at q>=2 and 64<=Y<=x, negativity of the
elementary odd endpoint limit gives an odd non-one prime at most x. Apply the
exact criterion and its elementary upper bound. No finite arithmetic sums remain. -/
theorem exists_odd_prime_not_one_of_oddEndpointElementaryLimit_neg {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y)
    (hYx : Y ≤ x) (hlim : oddEndpointElementaryLimit q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  have hy0 : 0 < Y := by linarith only [hY]
  exact
    exists_odd_prime_not_one_of_oddEndpointLimit_neg hq hGRH hp hne hinv hx hY hYx
      ((oddEndpointLimit_le_elementary q hx.le hy0).trans_lt hlim)

/-- For 0<q<=N,x>=1,Y>=64, the full endpoint limit is monotone in the level.
Pass the established positive-gap inequality to the common nontrivial right filter.
This supplies conductor monotonicity for gap-free witness criteria. -/
theorem fullEndpointLimit_mono_level {q N : ℕ} {x Y : ℝ} (hq : 0 < q) (hqN : q ≤ N) (hx : 1 ≤ x)
    (hY : 64 ≤ Y) :
    reciprocalGapFullEndpointLimit q x Y ≤ reciprocalGapFullEndpointLimit N x Y := by
  have he :
    (fun h : ℝ ↦ reciprocalGapFullEndpointSeparation h q x Y) ≤ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun h ↦ reciprocalGapFullEndpointSeparation h N x Y) :=
    Filter.Eventually.mono self_mem_nhdsWithin
      (fun h hh ↦ reciprocalGapFullEndpointSeparation_mono_level hh hx hY hq hqN)
  exact
    le_of_tendsto_of_tendsto (tendsto_reciprocalGapFullEndpointSeparation_right q hx Y)
      (tendsto_reciprocalGapFullEndpointSeparation_right N hx Y) he

/-- For 0<q<=N,x>=1,Y>=64, the elementary odd endpoint limit is monotone in
its level. The two-power corrections are independent of the level; apply the
full-limit comparison. This allows an original-level bound instead of conductor data. -/
theorem oddEndpointElementaryLimit_mono_level {q N : ℕ} {x Y : ℝ} (hq : 0 < q) (hqN : q ≤ N)
    (hx : 1 ≤ x) (hY : 64 ≤ Y) :
    oddEndpointElementaryLimit q x Y ≤ oddEndpointElementaryLimit N x Y := by
  unfold oddEndpointElementaryLimit
  exact add_le_add (add_le_add (fullEndpointLimit_mono_level hq hqN hx hY) (le_refl _)) (le_refl _)

end PseudoPrime.LLS.PaperStatements
