/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ExcludedCharacterDefect

/-! # Coprime and negative witnesses from exact excluded-support endpoint costs -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal GRH data and 64<=Y<=x, upper bounds c,D on
the exact excluded reciprocal and logarithmic defects and a negative endpoint
limit give an N-coprime non-one prime. Infer both character-sum bounds under
witness nonexistence and pass to the right endpoint. No gap or selected support
must be supplied, and no relation between q and N is required. -/
theorem exists_prime_coprime_not_one_of_excluded_two_cost_limit_neg {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y c D : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hC : excludedCharacterDefect χ N (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤ c)
    (hD : excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤ D)
    (hlim : oddEndpointTwoCostLimit q x Y c D < 0) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have he :=
    reciprocal_defect_eq_excluded_of_ambient_trivial χ (by linarith only [hY] : 0 ≤ Y)
      (fun p hp hpy hpc ↦ ht p hp (hpy.trans hYx) hpc)
  have hr :=
    AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000
      hGRH.riemann (by linarith only [hY] : 2 ≤ Y)
  have hlo : Real.log Y - (31551 / 20000 : ℝ) - c ≤ (characterReciprocalWeightedSum Y χ).re := by
    linarith only [he, hr, hC]
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hlo
  rw [reciprocalMassCap_sub_cost_eq] at hm
  have heD := logarithmic_defect_eq_excluded_of_ambient_trivial χ (zero_lt_one.trans hx).le ht
  have hlog := heD.le.trans hD
  have hnonneg :
    ∀ᶠ h : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 ≤ oddEndpointTwoCostSeparation h q x Y c D := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro h hh
    have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx.le hm
    have hL := reciprocalGapSum_re_ge_of_log_defect_le χ hh hx hGRH.riemann hlog
    let M := reciprocalGapReciprocalMassCap q Y (Real.log Y - (31551 / 20000 : ℝ))
    let C := c / (1 - 1 / Real.sqrt Y) ^ 2
    let A :=
      (x - Real.sqrt x / 20 - (1839 / 1000 : ℝ) * Real.log x - 21 / 20) /
        (Real.sqrt x * (1 + h * Real.log x))
    have heq :
      oddEndpointTwoCostSeparation h q x Y c D =
        2 * (M + C) + reciprocalGapEndpointMassBudget h q x (M + C) +
              reciprocalGapSignedGammaBudget h x -
            A +
          D / Real.sqrt x := by
      dsimp only [oddEndpointTwoCostSeparation, oddEndpointCostSeparation,
        reciprocalGapFullEndpointSeparation, reciprocalGapEndpointMassBudget, M, C, A]
      ring
    rw [heq]
    change
      (reciprocalGapCharacterSum h χ x).re ≤
        2 * (M + C) + reciprocalGapEndpointMassBudget h q x (M + C) +
          reciprocalGapSignedGammaBudget h x at hU
    change A - D / Real.sqrt x ≤ (reciprocalGapCharacterSum h χ x).re at hL
    linarith only [hU, hL]
  have hz : 0 ≤ oddEndpointTwoCostLimit q x Y c D :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (tendsto_oddEndpointTwoCostSeparation_right q hx.le Y c D) hnonneg
  exact (not_lt_of_ge hz) hlim

open AnalyticNumberTheory.Arithmetic in
/-- For a primitive quadratic character with q dividing N and 2 dividing N,
the exact two-cost endpoint condition yields an odd N-coprime negative prime.
Use the coprime non-one theorem, exclude two, and classify quadratic unit values.
The local defects retain cancellation before arithmetic cost estimates. -/
theorem exists_odd_prime_neg_one_of_excluded_two_cost_limit_neg {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x Y c D : ℝ} (hx : 1 < x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hC : excludedCharacterDefect χ N (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalWeightedMangoldtTerm Y) ≤ c)
    (hD : excludedCharacterDefect χ N (Finset.Ioc 0 ⌊x⌋₊) (logWeightedMangoldtTerm x) ≤ D)
    (hlim : oddEndpointTwoCostLimit q x Y c D < 0) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_excluded_two_cost_limit_neg hq hGRH hp hne hi hx hY hYx hC hD
      hlim
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
