/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPolePrimeTrivialBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GeneralTwoPoleWitness

/-! # Prime-base MR witnesses from a character-free two-pole separation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite n greater than one under GRH, positive character-free two-pole
separation yields a prime failing the strong Miller-Rabin test through the cutoff.
Universal prime passage forces a nonprincipal quotient character to be trivial on
every small prime, contradicting the scalar criterion. No uniform character budget
is left as a hypothesis. -/
theorem exists_prime_strong_witness_of_twoPolePrimeTrivialSeparation {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (S : Finset ℕ) (hS : ∀ k ∈ S, (k : ℝ) ≤ (99 / 40 : ℝ) * x)
    (hgap : 0 < LLS.twoPolePrimeTrivialSeparation n S x) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (99 / 40 : ℝ) * x ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  classical
  by_contra h
  have hpass :
    ∀ p : ℕ,
      p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
    fun p hp hb ↦ Classical.byContradiction (fun hf ↦ h ⟨p, hp, hb, hf⟩)
  obtain ⟨H, hH, hHpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨χ', hχz⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hz
  apply
    LLS.prime_trivial_false_of_twoPolePrimeTrivialSeparation (LLS.pullbackCharacter χ')
      (LLS.pullbackCharacter_ne_one_of_ne_one χ' hχz) hGRH hx S hS hgap
  intro p hp hb
  obtain ⟨u, hu, he⟩ := hHpass p (hpass p hp hb)
  rw [← he]
  exact LLS.pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.PrimeTestBounds.MillerRabin
