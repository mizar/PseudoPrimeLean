/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularSignedAverage
public import PseudoPrime.LLS.PaperStatements.MellinKernelPrimitiveSupport

/-! # Scale-one arithmetic credit for triangular averages -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- If every prime through the cutoff is coprime to the level and lies in the subgroup,
retain the finite level-one principal sum in the nonprincipal signed arithmetic average.
Apply the primitive average at scale one, separate the principal character, and use equality
of inverse-character real parts. The strict prime-factor bound preserves the cutoff endpoint. -/
theorem triangular18_scaleOne_pair_lower {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) {X : ℝ}
    (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    letI := Classical.propDecidable
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (2 : ℝ) * (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re) -
        2 * (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        ((∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
          (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re) := by
  classical
  let _ := Classical.propDecidable
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re
  have hd : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p := by
    intro p hp hpq
    exact (Nat.floor_lt hX).mpr (hlarge p hp hpq)
  have heq := MellinKernel.principal_sum_level_one_of_no_divisor K (q := q) 1 hd
  have hI : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have heq' :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) 1 n).re) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re := by
    have h := congrArg Complex.re heq
    simpa only [hI, Complex.re_sum] using h
  have hc :=
    MellinKernel.principal_sum_le_primitive_of_noSmall K H (x := 1) (by norm_num only) hsmall
  rw [heq'] at hc
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) 1 n).re :=
    congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K 1))
  have hr (χ : A) : (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter (by norm_num only)
  have hs :=
    Finset.sum_congr (s₁ := Finset.univ.erase (1 : A)) rfl
      (fun χ _ ↦ congrArg (fun y : ℝ ↦ F χ + y) (hr χ))
  change (2 : ℝ) * _ * _ - 2 * _ ≤ _
  rw [hs, Finset.sum_add_distrib]
  rw [hp] at he
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  linarith only [hc, he]

end PseudoPrime.LLS.PaperStatements
