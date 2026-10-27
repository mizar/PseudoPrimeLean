/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointTwoCostPolynomial
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.SharpTwoAdicCorrections

/-! # Endpoint witnesses with sharp two-adic logarithmic corrections -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Under GRH, a nonprincipal quadratic primitive associate with conductor at least two
has an odd non-one prime through x if the endpoint limit is negative. Inputs satisfy
64 ≤ Y ≤ x, with a reciprocal cost bound and any logarithmic defect bound valid under
odd-prime triviality. The right-limit comparison separates arithmetic from analysis. -/
theorem exists_odd_prime_of_twoCostLimit_neg_of_defect_bound {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c D : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hC : quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ c)
    (hD :
      (∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1) →
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x -
            (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.primitiveCharacter).re ≤
          D)
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
  have hlog := hD ht
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

open AnalyticNumberTheory.Arithmetic in
/-- For x ≥ 2, a quadratic primitive associate trivial on every odd prime through x
has logarithmic defect at most half the squared logarithm. Reduce the defect exactly
to powers of two and apply the sharp uniform branch bound. No GRH is required. -/
theorem log_defect_le_half_log_sq_of_quadratic {N : ℕ} (χ : DirichletCharacter ℂ N) {x : ℝ}
    (hx : 2 ≤ x) (hquad : χ.primitiveCharacter.IsQuadratic)
    (ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ.primitiveCharacter p = 1) :
    logWeightedMangoldtSum x - (characterLogWeightedSum x χ.primitiveCharacter).re ≤
      (Real.log x) ^ 2 / 2 := by
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 2).trans hx
  have ho :
    ∀ {k p : ℕ},
      k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊ →
        p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ → p.Prime → Odd p → χ.primitiveCharacter p = 1 := by
    intro k p hk hp hprime hodd
    exact ht p hprime hodd (cast_le_of_mem_root_cutoff hx1 (Finset.mem_Icc.mp hk).1 hp)
  rw [logWeightedMangoldtSum_sub_characterLogWeightedSum_re_eq_twoAdicCorrection_of_eq_one x χ hx
      ho]
  exact
    twoAdicLogCorrection_le_half_log_sq_of_isQuadratic x χ
      ((by norm_num only : (0 : ℝ) < 2).trans_le hx).ne' hquad

/-- Under GRH and the quadratic conductor hypotheses, a negative endpoint limit
with logarithmic cost half the squared logarithm yields an odd non-one prime.
Apply the generic defect criterion with the sharp two-adic comparison.
This strengthens the old minus-one branch without changing reciprocal inputs. -/
theorem exists_odd_prime_of_sharp_twoCostLimit_neg {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x Y c : ℝ} (hx : 1 < x)
    (hY : 64 ≤ Y) (hYx : Y ≤ x) (hC : quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ c)
    (hlim : oddEndpointTwoCostLimit χ.conductor x Y c ((Real.log x) ^ 2 / 2) < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ.primitiveCharacter p ≠ 1 := by
  have hx2 : 2 ≤ x := by linarith only [hY, hYx]
  exact
    exists_odd_prime_of_twoCostLimit_neg_of_defect_bound χ hq hne hquad hGRH hx hY hYx hC
      (fun ht ↦ log_defect_le_half_log_sq_of_quadratic χ hx2 hquad ht) hlim

/-- Under the same conductor and GRH hypotheses, a positive rational endpoint
polynomial at y ≥ 8 with logarithmic cost 2(log y)² gives an odd non-one prime
through y². Normalize the squared-cutoff logarithm and apply the sharp criterion.
This is the numerical certificate interface for improved witness radii. -/
theorem exists_odd_prime_of_sharp_twoCostPolynomial_pos {N : ℕ} (χ : DirichletCharacter ℂ N)
    [NeZero χ.conductor] (hq : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hquad : χ.primitiveCharacter.IsQuadratic)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y c : ℝ} (hy : 8 ≤ y)
    (hC : quadraticTwoReciprocalCost (χ.primitiveCharacter 2) ≤ c)
    (hP :
      0 <
        oddEndpointTwoCostPolynomial (Real.log χ.conductor) (2096 / 1831) y (Real.log y) c
          (2 * (Real.log y) ^ 2)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ y ^ 2 ∧ χ.primitiveCharacter p ≠ 1 := by
  have hy1 : 1 < y := by linarith only [hy]
  have hy64 : 64 ≤ y ^ 2 := by nlinarith only [hy]
  have hx : 1 < y ^ 2 := by linarith only [hy64]
  have he : (Real.log (y ^ 2)) ^ 2 / 2 = 2 * (Real.log y) ^ 2 := by
    rw [Real.log_pow]
    ring
  have hl := oddEndpointTwoCostLimit_neg_of_rational_polynomial_pos χ.conductor hy1 hP
  apply exists_odd_prime_of_sharp_twoCostLimit_neg χ hq hne hquad hGRH hx hy64 (le_refl _) hC
  rw [he]
  exact hl

end PseudoPrime.LLS.PaperStatements
