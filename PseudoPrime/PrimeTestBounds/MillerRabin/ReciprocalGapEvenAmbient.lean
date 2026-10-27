/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEvenOriginalLevel
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReciprocalGapAmbient
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.LLS.Theorem11S1Subgroup
public import PseudoPrime.PrimeTest.MillerRabin.WitnessBound
public import PseudoPrime.PrimeTest.MillerRabin.Composite

/-! # Even-parity savings for prime Miller–Rabin witness bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For every odd n>1, minus one passes the canonical strong test at j=0.
The odd residual exponent preserves minus one and the two-adic exponent is positive.
This forces any character trivial on passing residues to be even. -/
theorem strongMillerRabinPass_neg_one {n : ℕ} (hn : 1 < n) (ho : Odd n) :
    PrimeTest.StrongMillerRabinPass n (-1) := by
  have hd := PrimeTest.odd_sub_canonical_decomp hn ho
  refine Or.inr ⟨0, hd.1, ?_⟩
  rw [pow_zero, one_mul, hd.2.1.neg_one_pow]

/-- For odd n>1, a complex character trivial on all strong-test passing residues
is even, since minus one passes. No compositeness or primitivity is required.
This justifies the sharper parity-sensitive analytic budget for Miller–Rabin witnesses. -/
theorem character_even_of_trivial_on_pass {n : ℕ} (hn : 1 < n) (ho : Odd n)
    {χ : DirichletCharacter ℂ n}
    (hpass : ∀ a : ZMod n, PrimeTest.StrongMillerRabinPass n a → χ a = 1) : χ.Even :=
  hpass (-1) (strongMillerRabinPass_neg_one hn ho)

open PseudoPrime.LLS.PaperStatements in
/-- For odd N>1 and a nonprincipal character trivial on passing residues, GRH
and even ambient separation yield a coprime prime rejecting the canonical strong test
below x. Infer even parity from acceptance of minus one and retain it on normalization.
This uses the smaller even Gamma budget without discarding additional-nonunit losses. -/
theorem exists_prime_reject_of_character_even_ambient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hn : 1 < N) (ho : Odd N) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x) (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      reciprocalGapEvenAmbientRationalSeparation χ.conductor N x B₀ B₁ <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ)))
    (hpass : ∀ a : ZMod N, PrimeTest.StrongMillerRabinPass N a → χ a = 1) :
    let (s, d) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ x ∧
        Nat.Coprime p N ∧
        (p : ZMod N) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hpx, hpc, hv⟩ :=
    exists_prime_original_character_ne_one_of_reciprocalGap_even_ambient χ
      (character_even_of_trivial_on_pass hn ho hpass) hne hGRH hx B₀ B₁ B hB₀ hB₁ hB hcop lo u hlo
      hu hu1 hgap
  refine ⟨p, hp, hpx, hpc, ?_⟩
  exact PrimeTest.not_strongMillerRabinPass_iff.mp (fun ha ↦ hv (hpass p ha))

open PseudoPrime.LLS.PaperStatements in
/-- For an odd composite N>1 under GRH, even ambient separation for each divisor
q>=2 of N yields a coprime prime rejecting the canonical strong test below x.
Choose the existing nonprincipal character trivial on passing residues, infer its even
parity, and apply the sharper separation at its conductor. Numeric gaps remain premises. -/
theorem exists_prime_reject_of_even_ambient_divisor_separation {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x)
    (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N)
    (lo u : ℕ → ℝ) (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      ∀ d : ℕ,
        2 ≤ d →
          d ∣ N →
          reciprocalGapEvenAmbientRationalSeparation d N x B₀ B₁ <
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
    exists_prime_reject_of_character_even_ambient χ hn ho hne hGRH hx B₀ B₁ B hB₀ hB₁ hB hcop lo u
      hlo hu hu1 (hgap χ.conductor hq χ.conductor_dvd_level) hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
