/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapEndpointSelected

/-! # Original-level witnesses from selected endpoint-mass separation -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a nonprincipal character at original level N under GRH, positive h,
64<=Y<=x and selected N-coprime reciprocal and principal supports, endpoint
separation at its conductor yields an N-coprime non-one prime at most x.
Apply the primitive selected endpoint theorem and transfer values back on coprime
inputs. Neither primitivity nor a conductor nonzero premise is needed from callers. -/
theorem exists_prime_original_character_ne_one_of_reciprocalGap_endpoint_selected {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {h x Y : ℝ} (hh : 0 < h)
    (hx : 1 ≤ x) (hY : 64 ≤ Y) (hYx : Y ≤ x) (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hcopC : ∀ a ∈ C, Nat.Coprime a N) (B : Finset ℕ) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ a ∈ B, Nat.Coprime a N) (lo u : ℕ → ℝ)
    (hlo : ∀ a ∈ B, lo a ≤ ArithmeticFunction.vonMangoldt a) (hu : ∀ a ∈ B, ((a : ℝ) / x) ^ h ≤ u a)
    (hu1 : ∀ a ∈ B, u a ≤ 1)
    (hgap :
      reciprocalGapEndpointSelectedSeparation h χ.conductor N x Y C <
        ∑ a ∈ B, (lo a / Real.sqrt x) * ((1 - u a) / h)) :
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
    exists_prime_coprime_not_one_of_reciprocalGap_endpoint_selected hh hq χ.conductor_dvd_level hGRH
      hp hψ hi hx hY hYx C hC hcopC B hB hcop lo u hlo hu hu1 hgap
  have he := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ hpc.isCoprime
  simp only [Int.cast_natCast] at he
  refine ⟨p, hprime, hpx, hpc, ?_⟩
  intro hval
  exact hv (he.trans hval)

end PseudoPrime.LLS.PaperStatements
