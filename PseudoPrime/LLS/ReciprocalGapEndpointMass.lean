/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedEndpointDifference
public import PseudoPrime.LLS.ReciprocalGapCoupledBudgets
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleEndpointMass

/-! # Variable-gap character sums controlled by one endpoint zero mass -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Joint pole-left budget controlled by a single upper bound M on the endpoint
zero mass. The normalized conductor factor D=(1-x^(-h))/h occurs only as D and
(D+2)/(1+2h); there is no separate Euler endpoint or uncancelled inverse-gap factor.
Real operations are totalized; comparison theorems assume h>0,x>=1 and primitive GRH data. -/
noncomputable def reciprocalGapEndpointMassBudget (h : ℝ) (q : ℕ) (x M : ℝ) : ℝ :=
  (reciprocalGapLogQuotient h x * Real.log q / 2 +
      ((reciprocalGapLogQuotient h x + 2) / (1 + 2 * h)) * M) /
    Real.sqrt x

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data at q>=2,h>0,x>=1, a cap M on the absolute
Hadamard constant bounds the exact joint pole-left value. Apply the weighted endpoint
Poisson difference to the inverse character, identify its endpoint with the same
Hadamard mass, and use the nonnegative scalar coefficient. No Euler cap is required. -/
theorem reciprocalGap_pole_left_le_endpoint_mass {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x M : ℝ} (hx : 1 ≤ x) (hM : |primitiveBRe χ| ≤ M) :
    reciprocalGapPoleLeftValue h χ x ≤ reciprocalGapEndpointMassBudget h q x M := by
  have hi := DirichletCharacter.isPrimitive_inv hp
  have hni : χ⁻¹⁻¹ ≠ 1 := by simpa only [inv_inv] using hne
  have hw :=
    completedLogDeriv_endpoint_weighted_gap_le hq (hGRH q χ⁻¹ hi) hi hinv hni hh (x ^ (-h))
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  have he := completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log hq hGRH hi hinv hni
  rw [primitiveBRe_inv_eq hne] at he
  have hv : (logDeriv χ⁻¹.completedLFunction 1).re + Real.log q / 2 = |primitiveBRe χ| := by
    rw [he]
    ring
  rw [hv] at hw
  have hc :=
    mul_le_mul_of_nonneg_left hM
      (div_nonneg
        (by linarith only [reciprocalGapLogQuotient_nonneg hh hx] :
          0 ≤ reciprocalGapLogQuotient h x + 2)
        (by linarith only [hh] : 0 ≤ 1 + 2 * h))
  have hnorm :
    reciprocalGapPoleLeftValue h χ x =
      ((1 - x ^ (-h)) * Real.log q + (logDeriv χ⁻¹.completedLFunction 1).re -
          x ^ (-h) * (logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)).re) /
        h /
        Real.sqrt x := by
    unfold reciprocalGapPoleLeftValue
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hnorm]
  have hd := div_le_div_of_nonneg_right hw (Real.sqrt_nonneg x)
  have hb :=
    div_le_div_of_nonneg_right
      (add_le_add (le_refl (reciprocalGapLogQuotient h x * Real.log q / 2)) hc) (Real.sqrt_nonneg x)
  exact hd.trans hb

/-- Under primitive nonprincipal GRH data and an endpoint mass cap, the real
completed remainder is bounded by the joint endpoint-mass budget plus the signed
Gamma budget. Compose the contour decomposition with the normalized real-axis bound.
This preserves the signed Gamma saving and is uniform in the positive gap. -/
theorem reciprocalGap_remainder_re_le_endpoint_mass {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x M : ℝ} (hx : 1 ≤ x)
    (hM : |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| ≤ M) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x := by
  have hR := reciprocalGap_remainder_re_le_pole_left_value hh hp hne hinv hx
  exact
    hR.trans
      (add_le_add (reciprocalGap_pole_left_le_endpoint_mass hh hq hGRH hp hne hinv hx hM)
        (le_refl _))

open AnalyticNumberTheory.DirichletLFunction in
/-- Under primitive nonprincipal GRH data, q>=2,h>0,x>=1 and mass cap M, the real
finite character sum is at most 2M plus the joint endpoint-mass and signed Gamma
budgets. Compare the actual two-pole zero sum at Poisson width one half and combine
the remainder estimate. Neither a positive Euler offset nor its divergent cap is needed. -/
theorem reciprocalGapCharacterSum_re_le_endpoint_mass {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x M : ℝ} (hx : 1 ≤ x) (hM : |primitiveBRe χ| ≤ M) :
    (reciprocalGapCharacterSum h χ x).re ≤
      2 * M + reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x := by
  have hx0 := zero_lt_one.trans_le hx
  have hphase (ρ : ℂ) : ‖(x : ℂ) ^ (Complex.I * ρ.im)‖ ≤ 1 := (norm_real_mellin_phase hx0).le
  have hz :=
    twoPole_zeroSum_le_abs_BRe hq hGRH hp hne hinv (a := 1 / 2) (b := 1 / 2 + h)
      (by nlinarith only [hh]) _ hphase
  have he :
    (∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ) =
      ∑' ρ : ℂ,
        twoPoleCompletedZeroTerm χ (1 / 2) (1 / 2 + h) (fun z ↦ (x : ℂ) ^ (Complex.I * z.im)) ρ :=
    tsum_congr (fun ρ ↦ reciprocalGapMellinKernel_zeroTerm_eq hh χ x ρ)
  rw [← he] at hz
  have hr :=
    Complex.re_le_norm (-(∑' ρ : ℂ, (reciprocalGapMellinKernel h hh).oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hr
  have hR := reciprocalGap_remainder_re_le_endpoint_mass hh hq hGRH hp hne hinv hx hM
  rw [reciprocalGapCharacterSum_eq_zeroSum_add_remainder hh hq hGRH hp hne hinv hx, Complex.add_re,
    Complex.neg_re]
  linarith only [hz.2, hr, hR, hM]

end PseudoPrime.LLS.PaperStatements
