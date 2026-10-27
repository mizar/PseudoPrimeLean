/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointWitness
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalAmbientTriviality

/-! # Selected reciprocal prefixes for endpoint-mass witness separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Selected unsigned reciprocal prefix minus the exact additional nonunit loss.
Inputs q,N,Y,C are totalized. Under q dividing N, positive Y, N-coprime selected
support and prime triviality, this bounds the real reciprocal character sum below.
This retains original-level exclusions in the endpoint-mass input. -/
noncomputable def reciprocalGapSelectedReciprocalLower (q N : ℕ) (Y : ℝ) (C : Finset ℕ) : ℝ :=
  (∑ n ∈ C, AnalyticNumberTheory.Arithmetic.reciprocalWeightedMangoldtTerm Y n) -
    AnalyticNumberTheory.Arithmetic.additionalNonunitMangoldtPrefix q N (Finset.Ioc 0 ⌊Y⌋₊)
      (AnalyticNumberTheory.Arithmetic.reciprocalMangoldtFactor Y)

/-- Endpoint-mass upper budget with the selected reciprocal lower prefix and
the exact principal additional nonunit cost. Inputs h,q,N,x,Y,C are totalized.
Strict comparison with a selected principal lower sum is the witness criterion.
This definition packages scalar costs without any character-valued hypothesis. -/
noncomputable def reciprocalGapEndpointSelectedSeparation (h : ℝ) (q N : ℕ) (x Y : ℝ)
    (C : Finset ℕ) : ℝ :=
  let M := reciprocalGapReciprocalMassCap q Y (reciprocalGapSelectedReciprocalLower q N Y C)
  2 * M + reciprocalGapEndpointMassBudget h q x M + reciprocalGapSignedGammaBudget h x +
    reciprocalGapAdditionalNonunitWeight h q N x

open AnalyticNumberTheory.Arithmetic in
/-- Under primitive nonprincipal GRH data, q dividing N, positive h and 64<=Y<=x,
selected N-coprime supports at Y and x with certified weights and strict endpoint
separation produce an N-coprime non-one prime at most x. Infer the reciprocal
lower bound under witness nonexistence and apply the endpoint-mass theorem.
No unknown character sum or zero mass is assumed by the caller. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_endpoint_selected {h : ℝ} (hh : 0 < h)
    {q N : ℕ} [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x Y : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpy hpc
    by_contra hv
    exact hn ⟨p, hprime, hpy.trans hYx, hpc, hv⟩
  have hy0 : 0 < Y := by linarith only [hY]
  have hR := selected_reciprocal_sub_loss_le_character hqN χ hy0 C hC hcopC ht
  exact
    hn
      (exists_prime_coprime_not_one_of_reciprocalGap_endpoint_mass hh hq hqN hGRH hp hne hinv hx hY
        hR B hB hcop lo u hlo hu hu1 hgap)

/-- For a primitive nonprincipal quadratic character and 2 dividing N, the selected
endpoint separation produces an odd N-coprime prime at most x with value minus one.
Obtain the non-one witness, exclude two, and classify quadratic values.
This is the variable-gap negative-witness interface with explicit arithmetic inputs. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_endpoint_selected {h : ℝ} (hh : 0 < h) {q N : ℕ}
    [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x Y : ℝ} (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ n ∈ C, Nat.Coprime n N) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h q N x Y C <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_endpoint_selected hh hq hqN hGRH hp hne hi hx hY
      hYx C hC hcopC B hB hcop lo u hlo hu hu1 hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
