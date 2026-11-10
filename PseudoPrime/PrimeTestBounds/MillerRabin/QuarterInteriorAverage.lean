/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangularInterior
public import PseudoPrime.LLS.PaperStatements.ConductorSumComparison

/-! # Interior triangular annihilator bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, sum the interior triangular character bound over the nonprincipal
annihilator characters of a subgroup. Their primitive conductors and the
annihilator cardinality yield the conductor-log and index terms needed for the
middle-range arithmetic comparison. -/
theorem quarter_interior_annihilator (ha : 0 < a) {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hbound : Real.log x ≤ 2 * a) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := LLS.PaperStatements.triangularMellinKernel ha
    let S := Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H)
    (∑ i ∈ S, (∑' n : ℕ, K.summand i.val.primitiveCharacter x n).re) +
        (∑ i ∈ S, (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ x⁻¹ n).re) +
        2 * (∑ i ∈ S, (∑' n : ℕ, K.summand i.val.primitiveCharacter 1 n).re) ≤
      (4 * a - Real.log x) * LLS.PaperStatements.subgroupConductorLogSum H +
        (-6 * a + (3 / 2 : ℝ) * Real.log x + 18) * ((H.index : ℝ) - 1) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let f := fun χ : A ↦ χ.val.conductor
  let : ∀ χ : A, NeZero (f χ) := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  let S := Finset.univ.erase (1 : A)
  have hn (χ : A) (hχ : χ ∈ S) : χ.val ≠ 1 := by
    intro heq
    exact (Finset.mem_erase.mp hχ).1 (Subtype.ext heq)
  have hp (χ : A) (hχ : χ ∈ S) : χ.val.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val (hn χ hχ)
  have hs :=
    quarter_interior_family ha S f (fun χ ↦ χ.val.primitiveCharacter) hGRH
      (fun χ hχ ↦
        (by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
      (fun χ _ ↦ DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp
      (fun χ hχ ↦ inv_ne_one.mpr (hp χ hχ)) hx hbound
  have hcard : (S.card : ℝ) = (H.index : ℝ) - 1 := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  have hsum : (∑ χ ∈ S, Real.log (f χ)) = LLS.PaperStatements.subgroupConductorLogSum H := by
    unfold LLS.PaperStatements.subgroupConductorLogSum
    apply Finset.sum_congr ?_ (fun _ _ ↦ rfl)
    ext χ
    simp only [S, Finset.mem_erase, Finset.mem_univ, and_true]
  dsimp only at hs ⊢
  rw [hcard, hsum] at hs
  simpa only [S] using hs

end PseudoPrime.PrimeTestBounds.MillerRabin
