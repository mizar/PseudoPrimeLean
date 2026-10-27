/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEvenAmbientWitness

/-! # Return from primitive conductor to an arbitrary original character level -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For any even nonprincipal complex character at nonzero original level N under GRH,
ambient separation at its conductor with exclusion modulus N yields a coprime prime
p<=x where the original character is not one. Pass to the canonical primitive character,
retain the exact additional-prime losses, and transfer values back on N-coprime inputs.
The character need not be primitive and no conductor nonzero premise is required. -/
theorem exists_prime_original_character_ne_one_of_reciprocalGap_even_ambient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (he : χ.Even) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ a ∈ B₀, (a : ℝ) ≤ x) (hB₁ : ∀ a ∈ B₁, (a : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a)
    (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u a) (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      reciprocalGapEvenAmbientRationalSeparation χ.conductor N x B₀ B₁ <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  let _ : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let ψ := χ.primitiveCharacter
  have hp : ψ.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hψ : ψ ≠ 1 := by
    intro hv
    change χ.primitiveCharacter = 1 at hv
    have hc := DirichletCharacter.changeLevel_primitiveCharacter χ
    rw [hv, DirichletCharacter.changeLevel_one] at hc
    exact hne hc.symm
  have hq : 2 ≤ χ.conductor :=
    (Nat.two_le_iff _).mpr ⟨NeZero.ne _, fun he ↦ hψ (DirichletCharacter.level_one' ψ he)⟩
  have hi : ψ⁻¹ ≠ 1 := by
    intro hv
    have hh := congrArg (fun ξ : DirichletCharacter ℂ χ.conductor ↦ ξ⁻¹) hv
    exact hψ (by simpa only [inv_inv, inv_one] using hh)
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_even_ambient_lower hq χ.conductor_dvd_level hGRH
      (reciprocalGap_primitiveCharacter_even he) hp hψ hi hx B₀ B₁ B hB₀ hB₁ hB hcop lo u hlo hu hu1
      hgap
  have he := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hpc.isCoprime
  simp only [Int.cast_natCast] at he
  refine ⟨p, hprime, hpx, hpc, ?_⟩
  intro hval
  exact hv (he.trans hval)

end PseudoPrime.LLS.PaperStatements
