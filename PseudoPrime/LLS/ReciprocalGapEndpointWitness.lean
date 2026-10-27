/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointMass
public import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic
public import PseudoPrime.LLS.Extensions.RetainedEvenReciprocalBounds

/-! # Endpoint-mass witness criteria from reciprocal weighted sums -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Upper cap on endpoint zero mass obtained from a lower bound R for the reciprocal
weighted character sum at Y. Real division is totalized; the cap theorem assumes
Y>=64 and primitive nonprincipal GRH data. This supplies the mass input to gap kernels. -/
noncomputable def reciprocalGapReciprocalMassCap (q : ℕ) (Y R : ℝ) : ℝ :=
  ((1 / 2) * (1 - 1 / Y) * (Real.log q - Real.log Real.pi) - 1 / 4 - R) / (1 - 1 / Real.sqrt Y) ^ 2

/-- Endpoint mass cap obtained from the sharper reciprocal estimate for even
primitive characters. The analytic constant is `179/200` instead of `1/4`;
the reciprocal-sum lower bound `R` and endpoint scale remain explicit. This
cap is used by the parity-refined endpoint witness comparison. -/
noncomputable def reciprocalGapEvenReciprocalMassCap (q : ℕ) (Y R : ℝ) : ℝ :=
  ((1 / 2) * (1 - 1 / Y) * (Real.log q - Real.log Real.pi) - 179 / 200 - R) /
    (1 - 1 / Real.sqrt Y) ^ 2

open AnalyticNumberTheory.DirichletLFunction in
open AnalyticNumberTheory.Arithmetic in
/-- For primitive nonprincipal GRH data at q>=2 and Y>=64, a reciprocal-sum lower
bound R gives the endpoint-mass cap. Rearrange the existing raw reciprocal formula
using positivity of (1-1/sqrt Y)^2. Used by the two-pole witness comparison. -/
theorem reciprocalGap_mass_le_reciprocal_cap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {Y R : ℝ} (hY : 64 ≤ Y)
    (hR : R ≤ (characterReciprocalWeightedSum Y χ).re) :
    |primitiveBRe χ| ≤ reciprocalGapReciprocalMassCap q Y R := by
  have hY1 : 1 < Y := by linarith only [hY]
  have hs : 1 < Real.sqrt Y := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hY1
  have ht : 1 / Real.sqrt Y < 1 := (div_lt_one (zero_lt_one.trans hs)).mpr hs
  have hd : 0 < (1 - 1 / Real.sqrt Y) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht)
  have hr := primitiveReciprocalRaw hq hGRH hp hne hinv hY
  unfold reciprocalGapReciprocalMassCap
  apply (le_div_iff₀ hd).mpr
  linarith only [hr, hR]

open AnalyticNumberTheory.DirichletLFunction in
open AnalyticNumberTheory.Arithmetic in
/-- For primitive even nonprincipal GRH data at `q >= 2` and `Y >= 64`, a
reciprocal-sum lower bound `R` gives the parity-refined endpoint-mass cap.
Rearrange the even raw reciprocal estimate and divide by the positive squared
endpoint factor. -/
theorem reciprocalGap_mass_le_even_reciprocal_cap {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) {Y R : ℝ} (hY : 64 ≤ Y)
    (hR : R ≤ (characterReciprocalWeightedSum Y χ).re) :
    |primitiveBRe χ| ≤ reciprocalGapEvenReciprocalMassCap q Y R := by
  have hY1 : (1 : ℝ) < Y := by linarith only [hY]
  have hs : 1 < Real.sqrt Y := by simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt zero_le_one hY1
  have ht : 1 / Real.sqrt Y < 1 := (div_lt_one (zero_lt_one.trans hs)).mpr hs
  have hd : 0 < (1 - 1 / Real.sqrt Y) ^ 2 := sq_pos_of_pos (sub_pos.mpr ht)
  have hr := Extensions.primitiveReciprocalRaw_even_le_neg_179_div_200 hq hGRH hp hne heven hY
  unfold reciprocalGapEvenReciprocalMassCap
  apply (le_div_iff₀ hd).mpr
  linarith only [hr, hR]

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive GRH data, q dividing N, positive gap, x>=1 and Y>=64, a
reciprocal lower bound and strict scalar separation produce an N-coprime non-one
prime at most x. Compare the selected principal lower sum, with its exact exclusion
loss, against the endpoint-mass upper sum. No Euler offset or Euler caps are needed. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_endpoint_mass {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y R : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y)
    (hR : R ≤ (characterReciprocalWeightedSum Y χ).re) (B : Finset ℕ) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      2 * reciprocalGapReciprocalMassCap q Y R +
          reciprocalGapEndpointMassBudget h q x (reciprocalGapReciprocalMassCap q Y R) +
          reciprocalGapSignedGammaBudget h x +
          reciprocalGapAdditionalNonunitWeight h q N x <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hm := reciprocalGap_mass_le_reciprocal_cap hq hGRH hp hne hinv hY hR
  have hU := reciprocalGapCharacterSum_re_le_endpoint_mass hh hq hGRH hp hne hinv hx hm
  have hL :=
    selected_reciprocalGap_lower_sub_loss_le_character hqN hh.le (zero_lt_one.trans_le hx) χ hsmall
      B hB hcop lo u hlo hu hu1
  linarith only [hU, hL, hgap]

open AnalyticNumberTheory.Arithmetic in
/-- For a primitive nonprincipal quadratic character, the endpoint-mass separation
and 2 dividing N produce an odd N-coprime prime at most x with value minus one.
Apply the coprime non-one theorem and classify quadratic values; exclusion of two
gives oddness. This is the negative-witness interface for quadratic characters. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_endpoint_mass {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x Y R : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y)
    (hR : R ≤ (characterReciprocalWeightedSum Y χ).re) (B : Finset ℕ) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      2 * reciprocalGapReciprocalMassCap q Y R +
          reciprocalGapEndpointMassBudget h q x (reciprocalGapReciprocalMassCap q Y R) +
          reciprocalGapSignedGammaBudget h x +
          reciprocalGapAdditionalNonunitWeight h q N x <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_endpoint_mass hh hq hqN hGRH hp hne hi hx hY hR B
      hB hcop lo u hlo hu hu1 hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
