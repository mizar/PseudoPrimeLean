/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointArithmetic
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Odd-prime non-one endpoint witnesses with only two-power correction costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Additional mass cap for excluding prime two: twice its reciprocal weighted
sum divided by the positive reciprocal-formula denominator. Real operations are
totalized; witness theorems assume Y>=64. No original modulus occurs in this cost. -/
noncomputable def oddEndpointMassCorrection (Y : ℝ) : ℝ :=
  2 * AnalyticNumberTheory.Arithmetic.commonFactorReciprocalWeightedSum Y 2 /
    (1 - 1 / Real.sqrt Y) ^ 2

/-- Full-prime endpoint separation plus the two-power reciprocal mass correction
and twice the two-part logarithmic principal loss. Inputs h,q,x,Y are totalized.
Strict negativity for positive h and 64<=Y<=x produces an odd non-one prime.
All exclusion costs depend only on prime two, not on the factorization of q. -/
noncomputable def oddEndpointSeparation (h : ℝ) (q : ℕ) (x Y : ℝ) : ℝ :=
  reciprocalGapFullEndpointSeparation h q x Y +
    (2 + (reciprocalGapLogQuotient h x + 2) / (1 + 2 * h) / Real.sqrt x) *
      oddEndpointMassCorrection Y +
    2 * AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x 2 / Real.sqrt x

open AnalyticNumberTheory.Arithmetic in
/-- For arbitrary q,Y, subtracting the twice-two-part reciprocal loss from the
reciprocal lower input adds exactly the mass correction to the cap. Expand the
totalized divisions and rearrange. No denominator positivity is needed for this identity. -/
theorem oddEndpoint_mass_cap_eq (q : ℕ) (Y : ℝ) :
    reciprocalGapReciprocalMassCap q Y
        (Real.log Y - (31551 / 20000 : ℝ) - 2 * commonFactorReciprocalWeightedSum Y 2) =
      reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ)) +
        oddEndpointMassCorrection Y := by
  unfold reciprocalGapReciprocalMassCap oddEndpointMassCorrection
  simp only [div_eq_mul_inv]
  ring

open AnalyticNumberTheory.Arithmetic in
open AnalyticNumberTheory.RiemannZeta in
/-- For primitive nonprincipal GRH data at q>=2,h>0 and 64<=Y<=x, negative odd
endpoint separation produces an odd non-one prime at most x. Under nonexistence
use only two-power losses in both arithmetic lower bounds, then compare the mass
upper bound. Zero-valued primes are allowed; coprimality is not required. -/
theorem exists_odd_prime_not_one_of_oddEndpointSeparation_neg {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hgap : oddEndpointSeparation h q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → Odd p → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp ho hpx
    by_contra hv
    exact hn ⟨p, hp, ho, hpx, hv⟩
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have hy0 : 0 < Y := by linarith only [hY]
  have hr :=
    reciprocalSum_re_ge_of_odd_prime_trivial χ hy0 (fun p hp ho hpy ↦ ht p hp ho (hpy.trans hYx))
  have hr0 := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hGRH.riemann hy2
  have hlo :
    Real.log Y - (31551 / 20000 : ℝ) - 2 * commonFactorReciprocalWeightedSum Y 2 ≤
      (characterReciprocalWeightedSum Y χ).re := by
    linarith only [hr, hr0]
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hlo
  rw [oddEndpoint_mass_cap_eq] at hm
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
  have hL := reciprocalGapSum_re_ge_of_odd_prime_trivial χ hh hx hGRH.riemann ht
  let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  let C := oddEndpointMassCorrection Y
  let A :=
    (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
      (Real.sqrt x * (1 + h * Real.log x))
  have he :
    oddEndpointSeparation h q x Y =
      2 * (M + C) + reciprocalGapEndpointMassBudget h q x (M + C) +
            reciprocalGapSignedGammaBudget h x -
          A +
        2 * commonFactorLogWeightedSum x 2 / Real.sqrt x := by
    dsimp only [oddEndpointSeparation, reciprocalGapFullEndpointSeparation,
      reciprocalGapEndpointMassBudget, M, C, A]
    ring
  rw [he] at hgap
  change
    (reciprocalGapCharacterSum h χ x).re ≤
      2 * (M + C) + reciprocalGapEndpointMassBudget h q x (M + C) +
        reciprocalGapSignedGammaBudget h x at hU
  change
    A - 2 * commonFactorLogWeightedSum x 2 / Real.sqrt x ≤
      (reciprocalGapCharacterSum h χ x).re at hL
  linarith only [hU, hL, hgap]

/-- Right-limit odd-prime separation with the normalized quotient replaced by
log x. Inputs q,x,Y are totalized. It keeps the reciprocal and principal costs
for two and supplies a gap-free sufficient condition for an odd non-one witness. -/
noncomputable def oddEndpointLimit (q : ℕ) (x Y : ℝ) : ℝ :=
  reciprocalGapFullEndpointLimit q x Y +
    (2 + (Real.log x + 2) / Real.sqrt x) * oddEndpointMassCorrection Y +
    2 * AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x 2 / Real.sqrt x

/-- For fixed q,Y and x>=1, the odd endpoint separation tends from the right to
the stated limit. Combine the full-prime limit with the rational coefficient limit.
The two-power costs are independent of the gap, so no arithmetic sum is interchanged. -/
theorem tendsto_oddEndpointSeparation_right (q : ℕ) {x : ℝ} (hx : 1 ≤ x) (Y : ℝ) :
    Filter.Tendsto (fun h : ℝ ↦ oddEndpointSeparation h q x Y) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (oddEndpointLimit q x Y)) := by
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
  dsimp only [oddEndpointSeparation, oddEndpointLimit]
  exact
    ((tendsto_reciprocalGapFullEndpointSeparation_right q hx Y).add
          (((hc.div_const (Real.sqrt x)).const_add 2).mul_const
            (oddEndpointMassCorrection Y))).add_const
      _

/-- For primitive nonprincipal GRH data at q>=2 and 64<=Y<=x, a negative odd
endpoint limit gives an odd non-one prime at most x. Extract a positive gap along
the right filter and invoke the positive-gap theorem. This removes gap selection. -/
theorem exists_odd_prime_not_one_of_oddEndpointLimit_neg {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y)
    (hYx : Y ≤ x) (hlim : oddEndpointLimit q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  have hn : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), oddEndpointSeparation h q x Y < 0 :=
    (tendsto_oddEndpointSeparation_right q hx.le Y).eventually (Iio_mem_nhds hlim)
  have hp0 : ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < h := self_mem_nhdsWithin
  obtain ⟨h, hh, hs⟩ := (hp0.and hn).exists
  exact exists_odd_prime_not_one_of_oddEndpointSeparation_neg hh hq hGRH hp hne hinv hx hY hYx hs

end PseudoPrime.LLS.PaperStatements
