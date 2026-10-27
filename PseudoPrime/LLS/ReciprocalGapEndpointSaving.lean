/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointWitness
public import PseudoPrime.LLS.ParameterizedPart1Saving
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.FinerLLSConstants

/-! # Endpoint-mass witnesses with reciprocal saving inferred from nonexistence -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.Arithmetic in
/-- For primitive nonprincipal GRH data, positive gap, 64<=Y<=x, an unsigned
reciprocal lower bound with loss r and the stated scalar separation yield a
q-coprime non-one prime at most x. Under witness nonexistence the character sum
inherits max(0,log Y-r-primeFactorLogSum q); apply the endpoint-mass criterion.
The lower input is unsigned, so no unknown character sum remains as a hypothesis. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_reciprocal_saving {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y r : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (hrecip : Real.log Y - r ≤ reciprocalWeightedMangoldtSum Y) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      let R := max 0 (Real.log Y - r - primeFactorLogSum q)
      2 * reciprocalGapReciprocalMassCap q Y R +
          reciprocalGapEndpointMassBudget h q x (reciprocalGapReciprocalMassCap q Y R) +
          reciprocalGapSignedGammaBudget h x +
          reciprocalGapAdditionalNonunitWeight h q q x <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ Y → χ p = 1 := by
    intro p hprime hpc hpy
    by_contra hv
    exact hn ⟨p, hprime, hpy.trans hYx, hprime.coprime_iff_not_dvd.mpr hpc, hv⟩
  have hy0 : 0 < Y := by linarith only [hY]
  have hR := characterReciprocalWeightedSum_re_ge_of_reciprocal_lower χ hy0 hrecip ht
  exact
    hn
      (exists_prime_coprime_not_one_of_reciprocalGap_endpoint_mass hh hq (dvd_refl q) hGRH hp hne
        hinv hx hY hR B hB hcop lo u hlo hu hu1 hgap)

open AnalyticNumberTheory.Arithmetic AnalyticNumberTheory.RiemannZeta in
/-- Under the same primitive GRH and cutoff conditions, the certified reciprocal
loss 31551/20000 supplies the scalar witness criterion. Specialize the arbitrary
reciprocal-loss theorem with the existing RH lower bound. No finite modulus
certificate is required; only the explicit scalar separation remains to verify. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_fine_reciprocal {h : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      let R := max 0 (Real.log Y - (31551 / 20000 : ℝ) - primeFactorLogSum q)
      2 * reciprocalGapReciprocalMassCap q Y R +
          reciprocalGapEndpointMassBudget h q x (reciprocalGapReciprocalMassCap q Y R) +
          reciprocalGapSignedGammaBudget h x +
          reciprocalGapAdditionalNonunitWeight h q q x <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p ≠ 1 := by
  have hy2 : (2 : ℝ) ≤ Y := by linarith only [hY]
  have hr := reciprocalWeightedMangoldtSum_ge_log_sub_31551_div_20000 hGRH.riemann hy2
  exact
    exists_prime_coprime_not_one_of_reciprocalGap_reciprocal_saving hh hq hGRH hp hne hinv hx hY hYx
      hr B hB hcop lo u hlo hu hu1 hgap

end PseudoPrime.LLS.PaperStatements
