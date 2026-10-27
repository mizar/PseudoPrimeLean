/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointSelected
public import PseudoPrime.LLS.ReciprocalGapLogarithmicLower

/-! # Endpoint-mass witnesses with an analytic logarithmic principal lower bound -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal GRH data, q dividing N, h>0 and 64<=Y<=x,
selected N-coprime reciprocal support and strict separation against the analytic
logarithmic lower bound yield an N-coprime non-one prime at most x.
Infer reciprocal mass under witness nonexistence and use the RH principal lower
bound. No selected principal support or unknown character sum is required. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_endpoint_analytic {h : ℝ} (hh : 0 < h)
    {q N : ℕ} [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
            commonFactorLogWeightedSum x N) /
          (Real.sqrt x * (1 + h * Real.log x))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hy0 : 0 < Y := by linarith only [hY]
  have hR :=
    selected_reciprocal_sub_loss_le_character hqN χ hy0 C hC hcopC
      (fun p hp hpy hpc ↦ ht p hp (hpy.trans hYx) hpc)
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
  have hL := reciprocalGapCharacterSum_re_ge_logarithmic_analytic hqN χ hh hx hGRH.riemann ht
  dsimp only [reciprocalGapEndpointSelectedSeparation, reciprocalGapSelectedReciprocalLower] at hgap
  linarith only [hU, hL, hgap]

open AnalyticNumberTheory.Arithmetic in
/-- For a primitive nonprincipal quadratic character, 2 dividing N and the same
analytic endpoint separation, obtain an odd N-coprime prime at most x of value
minus one. Apply the non-one theorem, exclude two and classify quadratic values.
This keeps the principal lower bound analytic throughout the positive-gap range. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_endpoint_analytic {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x Y : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20 -
            commonFactorLogWeightedSum x N) /
          (Real.sqrt x * (1 + h * Real.log x))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_endpoint_analytic hh hq hqN hGRH hp hne hi hx hY
      hYx C hC hcopC hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
