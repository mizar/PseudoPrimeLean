/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointOriginalLevel
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapAmbient

/-! # Miller-Rabin witnesses from selected endpoint zero-mass separation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

open PseudoPrime.LLS.PaperStatements in
/-- For a nonprincipal original-level character trivial on passing residues, GRH,
positive gap and selected endpoint-mass separation yield a coprime prime rejecting
the canonical strong test at most x. Apply the original-level character theorem
and contradict acceptance. Reciprocal and principal exclusion losses stay explicit. -/
theorem exists_prime_reject_of_character_endpoint_selected {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x Y : ℝ} (hh : 0 < h)
    (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hcopC : ∀ a ∈ C, Nat.Coprime a N) (B : Finset ℕ) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a) (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ h ≤ u a)
    (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h χ.conductor N x Y C <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / h))
    (hpass : ∀ a : ZMod N, PrimeTest.StrongMillerRabinPass N a → χ a = 1) :
    let (s, d) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧
        Nat.Coprime p N ∧
        (p : ZMod N) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hpx, hpc, hv⟩ :=
    exists_prime_original_character_ne_one_of_reciprocalGap_endpoint_selected χ hne hGRH hh hx hY
      hYx C hC hcopC B hB hcop lo u hlo hu hu1 hgap
  refine ⟨p, hp, hpx, hpc, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mp (fun ha ↦ hv (hpass p ha))

open PseudoPrime.LLS.PaperStatements in
/-- For an odd composite N>1 under GRH, selected endpoint-mass separation for every
divisor d>=2 of N yields a coprime rejecting prime at most x. Choose the nonprincipal
character trivial on passing residues and specialize at its conductor.
This sufficient criterion has arbitrary positive gap and no unknown character sum. -/
theorem exists_prime_reject_of_endpoint_selected_divisor_separation {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {h x Y : ℝ} (hh : 0 < h) (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ)
    (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊) (hcopC : ∀ a ∈ C, Nat.Coprime a N) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a) (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ h ≤ u a)
    (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      ∀ d : ℕ,
        2 ≤ d →
          d ∣ N →
          reciprocalGapEndpointSelectedSeparation h d N x Y C <
            ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / h)) :
    let (s, d) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧
        Nat.Coprime p N ∧
        (p : ZMod N) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨χ, hne, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr
      ⟨χ.conductor_ne_zero, fun he ↦ hne (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr he)⟩
  exact
    exists_prime_reject_of_character_endpoint_selected χ hne hGRH hh hx hY hYx C hC hcopC B hB hcop
      lo u hlo hu hu1 (hgap χ.conductor hq χ.conductor_dvd_level) hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
