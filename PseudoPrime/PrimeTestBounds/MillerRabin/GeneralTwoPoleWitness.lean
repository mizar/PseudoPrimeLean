/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GeneralTwoPoleGammaWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaComparison
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Prime-base Miller-Rabin witnesses from general paired Euler bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For a nonprincipal character taking value one on every strong Miller-Rabin
pass, GRH and positive general two-pole separation produce a prime failing the
strong test through the ramp cutoff. The character prime witness cannot pass.
This transfers the general-character analytic criterion to prime-base MR rejection. -/
theorem exists_prime_strong_witness_of_generalTwoPole {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n) (hne : χ ≠ 1)
    (hχpass : ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → χ z = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < LLS.generalTwoPoleGammaSeparation χ S x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, _, hb, hv⟩ := LLS.exists_prime_not_one_of_generalTwoPole χ hne hGRH hx S hS hgap
  exact ⟨p, hp, hb, fun hpass ↦ hv (hχpass p hpass)⟩

/-- If a subgroup contains every strong pass and a nonprincipal character is
trivial on that subgroup, positive general two-pole separation supplies a prime
strong witness. Pass containment forces character value one, contrary to the
analytic witness. The subgroup and character may be chosen independently. -/
theorem exists_prime_strong_witness_of_subgroup_generalTwoPole {n : ℕ} [NeZero n]
    (H : Subgroup (ZMod n)ˣ)
    (hHpass :
      ∀ z : ZMod n, PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z)
    (χ : DirichletCharacter ℂ n) (hne : χ ≠ 1) (hχH : ∀ u : (ZMod n)ˣ, u ∈ H → χ (u : ZMod n) = 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < LLS.generalTwoPoleGammaSeparation χ S x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_strong_witness_of_generalTwoPole χ hne ?_ hGRH hx S hS hgap
  intro z hz
  obtain ⟨u, hu, he⟩ := hHpass z hz
  rw [← he]
  exact hχH u hu

/-- For odd composite n greater than one under GRH, positive two-pole separation
for every nonprincipal character gives a prime strong witness through the cutoff.
Choose a proper pass-containing subgroup and a nonprincipal quotient character.
This closes the MR connection while leaving the uniform scalar estimate explicit. -/
theorem exists_prime_strong_witness_of_uniform_generalTwoPole {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : ∀ χ : DirichletCharacter ℂ n, χ ≠ 1 → 0 < LLS.generalTwoPoleGammaSeparation χ S x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨χ', hχz⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hz
  have hne := LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz
  exact
    exists_prime_strong_witness_of_subgroup_generalTwoPole H hHpass (LLS.pullbackCharacter χ') hne
      (fun _ hu ↦ LLS.pullbackCharacter_eq_one_of_mem χ' hu) hGRH hx S hS (hgap _ hne)

end PseudoPrime.PrimeTestBounds.MillerRabin
