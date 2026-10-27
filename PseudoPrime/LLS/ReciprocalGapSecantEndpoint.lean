/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapSecantLower
public import PseudoPrime.LLS.ReciprocalGapFullEndpointMonotone

/-! # Endpoint-mass witnesses with the exact logarithmic secant coefficient -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The full-prime endpoint upper budget minus the secant-scaled RH principal lower.
The endpoint mass cap and signed Gamma cost are unchanged. Inputs h,q,x,Y are totalized.
Strict negativity is used for exclusion-free witnesses, including rejecting MR prime bases. -/
noncomputable def reciprocalGapFullSecantSeparation (h : ℝ) (q : ℕ) (x Y : ℝ) : ℝ :=
  let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
  2 * M + reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x -
    reciprocalGapLogSecant h x * (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
      Real.sqrt x

/-- For primitive nonprincipal GRH data, positive h and 64<=Y<=x, strict secant
endpoint separation gives a non-one prime through x. Under witness nonexistence both
character sums are principal; combine the endpoint mass cap with the secant RH lower.
Values zero remain valid witnesses in this full-prime theorem. -/
theorem exists_prime_not_one_of_reciprocalGap_full_secant {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hgap : reciprocalGapFullSecantSeparation h q x Y < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hv
    exact hn ⟨p, hp, hpx, hv⟩
  have he :=
    reciprocalSum_re_eq_of_full_prime_trivial χ (by linarith only [hY] : 0 ≤ Y)
      (fun p hp hpy ↦ ht p hp (hpy.trans hYx))
  have hR :=
    AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
      hGRH.riemann (by linarith only [hY] : (2 : ℝ) ≤ Y)
  rw [← he] at hR
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
  have hl := reciprocalGap_principal_ge_secant_analytic hh hx hGRH.riemann
  rw [← reciprocalGapSum_re_eq_of_full_prime_trivial χ (zero_lt_one.trans hx).le ht] at hl
  dsimp only [reciprocalGapFullSecantSeparation] at hgap
  linarith only [hU, hl, hgap]

/-- For h>0,x>=1,Y>=64 and positive q<=N, the secant separation at q is at
most that at N. The new principal lower is independent of the level. Transfer the
existing endpoint conductor monotonicity. This removes divisor-wise numerical premises. -/
theorem reciprocalGapFullSecantSeparation_mono_level {h x Y : ℝ} (hh : 0 < h) (hx : 1 ≤ x)
    (hY : 64 ≤ Y) {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N) :
    reciprocalGapFullSecantSeparation h q x Y ≤ reciprocalGapFullSecantSeparation h N x Y := by
  have hb := reciprocalGapFullEndpointSeparation_mono_level hh hx hY hq hqN
  dsimp only [reciprocalGapFullSecantSeparation, reciprocalGapFullEndpointSeparation] at hb ⊢
  linarith only [hb]

/-- For x at least 64, the rational logarithmic RH lower profile is positive.
Use the logarithmic tangent at sixteen and sqrt x<=x. This ensures that the strict
coefficient improvement produces a strict improvement of the scalar witness criterion. -/
theorem logarithmicPrincipalProfile_pos_of_sixty_four {x : ℝ} (hx : 64 ≤ x) :
    0 < x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 := by
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hs : Real.sqrt x ≤ x := Real.sqrt_le_self_iff.mpr (Or.inr hx1)
  have ht :=
    Real.log_le_sub_one_of_pos
      (div_pos (zero_lt_one.trans_le hx1) (by norm_num only : (0 : ℝ) < 16))
  rw [Real.log_div (zero_lt_one.trans_le hx1).ne' (by norm_num only : (16 : ℝ) ≠ 0),
    show (16 : ℝ) = 2 ^ 4 by norm_num only, Real.log_pow] at ht
  norm_num only [Nat.cast_ofNat] at ht
  linarith only [hx, hs, ht, Real.log_two_lt_d9]

/-- For h>0 and x>=64, the new full endpoint separation is strictly below the old
one for every q and Y. Apply the strict secant comparison to the positive RH profile.
This preserves all previous successful scalar certificates and improves the criterion. -/
theorem reciprocalGapFullSecantSeparation_lt_old {h x Y : ℝ} (hh : 0 < h) (hx : 64 ≤ x) (q : ℕ) :
    reciprocalGapFullSecantSeparation h q x Y < reciprocalGapFullEndpointSeparation h q x Y := by
  have hl :=
    reciprocalGapSecant_lower_gt_fraction hh (by linarith only [hx] : 1 < x)
      (logarithmicPrincipalProfile_pos_of_sixty_four hx)
  dsimp only [reciprocalGapFullSecantSeparation, reciprocalGapFullEndpointSeparation]
  linarith only [hl]

/-- For primitive nonprincipal GRH data, q dividing N, h>0 and 64<=Y<=x,
selected N-coprime reciprocal support and secant analytic separation yield an N-coprime
non-one prime at most x. Retain the exact common-factor and additional nonunit losses.
No enumerated principal support or character-sum premise is needed. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_endpoint_secant {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        reciprocalGapLogSecant h x *
            (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
              AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x N) /
          Real.sqrt x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hy0 : 0 < Y := by linarith only [hY]
  have hR :=
    AnalyticNumberTheory.Arithmetic.selected_reciprocal_sub_loss_le_character hqN χ hy0 C hC hcopC
      (fun p hp hpy hpc ↦ ht p hp (hpy.trans hYx) hpc)
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
  have hL := reciprocalGapCharacterSum_re_ge_secant_analytic hqN χ hh hx hGRH.riemann ht
  dsimp only [reciprocalGapEndpointSelectedSeparation, reciprocalGapSelectedReciprocalLower] at hgap
  linarith only [hU, hL, hgap]

/-- For a primitive nonprincipal quadratic character under GRH, two dividing N
and the secant endpoint separation give an odd N-coprime prime with value minus one.
Apply the non-one result, exclude zero and two, and classify quadratic values.
This connects the variable-gap secant improvement to negative unit-prime witnesses. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_endpoint_secant {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        reciprocalGapLogSecant h x *
            (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
              AnalyticNumberTheory.Arithmetic.commonFactorLogWeightedSum x N) /
          Real.sqrt x) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_endpoint_secant hh hq hqN hGRH hp hne hi hx hY hYx
      C hC hcopC hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
