/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapOriginalLevel
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.PrimeTest.MillerRabin.WitnessBound
public import PseudoPrime.PrimeTest.MillerRabin.Composite

/-! # Reciprocal-gap bounds for prime Miller–Rabin witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite n>1, construct a nonprincipal complex character equal to one
on every strong Miller–Rabin passing residue. Use a nontrivial character of the quotient
by a proper subgroup containing those residues. This supplies the original-level
character for analytic witness bounds without a small-prime-divisor exclusion. -/
theorem exists_character_trivial_on_pass {n : ℕ} [NeZero n] (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) :
    ∃ χ : DirichletCharacter ℂ n,
      χ ≠ 1 ∧ ∀ a : ZMod n, PrimeTest.StrongMillerRabinPass n a → χ a = 1 := by
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn ho hc
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod n)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx⟩ := exists_ne (1 : (ZMod n)ˣ ⧸ H)
  obtain ⟨ψ, hψ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod n)ˣ ⧸ H) ℂ hx
  refine ⟨LLS.pullbackCharacter ψ, LLS.pullbackCharacter_ne_one_of_ne_one ψ hψ, ?_⟩
  intro a ha
  obtain ⟨u, hu, hua⟩ := hpass a ha
  rw [← hua]
  exact LLS.pullbackCharacter_eq_one_of_mem ψ hu

open PseudoPrime.LLS.PaperStatements in
/-- For a nonprincipal character trivial on passing residues, GRH and the finite
ambient reciprocal-gap separation yield a coprime prime rejecting the canonical strong
test below x. Extract the original-level character witness and contradict acceptance.
The exact additional-nonunit losses remain in the separation premise. -/
theorem exists_prime_reject_of_character_ambient {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hne : χ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x) (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      reciprocalGapAmbientRationalSeparation χ.conductor N x B₀ B₁ <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ)))
    (hpass : ∀ a : ZMod N, PrimeTest.StrongMillerRabinPass N a → χ a = 1) :
    let (s, d) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧
        Nat.Coprime p N ∧
        (p : ZMod N) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hpx, hpc, hv⟩ :=
    exists_prime_original_character_ne_one_of_reciprocalGap_ambient χ hne hGRH hx B₀ B₁ B hB₀ hB₁ hB
      hcop lo u hlo hu hu1 hgap
  refine ⟨p, hp, hpx, hpc, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mp (fun ha ↦ hv (hpass p ha))

open PseudoPrime.LLS.PaperStatements in
/-- For an odd composite N>1 under GRH, separation for every divisor d>=2 of N
yields a coprime prime rejecting the canonical strong test below x. Choose a character
trivial on passing residues and apply the separation at its conductor. The finite
supports are arbitrary; this is a sufficient analytic criterion, not a numeric cutoff. -/
theorem exists_prime_reject_of_ambient_divisor_separation {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x)
    (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N)
    (lo u : ℕ → ℝ) (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      ∀ d : ℕ,
        2 ≤ d →
          d ∣ N →
          reciprocalGapAmbientRationalSeparation d N x B₀ B₁ <
            ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ))) :
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
    exists_prime_reject_of_character_ambient χ hne hGRH hx B₀ B₁ B hB₀ hB₁ hB hcop lo u hlo hu hu1
      (hgap χ.conductor hq χ.conductor_dvd_level) hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
