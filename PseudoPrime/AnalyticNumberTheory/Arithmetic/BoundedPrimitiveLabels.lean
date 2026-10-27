/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveCharacterLabels

/-! # Primitive character labels at a bounded conductor scale -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a character at nonzero level `q <= Q`, retain its primitive character at
the conductor index `conductor - 1` in `Fin Q`. Transport the character along the
successor identity. The result matches the conductor indexing of the family zero ledger. -/
noncomputable def boundedPrimitiveCharacterLabel {q Q : ℕ} [NeZero q] (hq : q ≤ Q)
    (χ : DirichletCharacter ℂ q) : Σ d : Fin Q, DirichletCharacter ℂ (d.val + 1) := by
  let d : Fin Q :=
    ⟨χ.conductor - 1,
      (Nat.sub_lt (Nat.pos_of_ne_zero χ.conductor_ne_zero) (by norm_num only)).trans_le
        ((Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level).trans hq)⟩
  have he : d.val + 1 = χ.conductor :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero)
  exact ⟨d, cast (congrArg (DirichletCharacter ℂ) he.symm) χ.primitiveCharacter⟩

/-- Forget the upper bound on a successor-indexed character label while retaining
its numerical level and character. This recovers the unbounded primitive label
and allows exact comparison of finite weighted family sums. -/
def forgetBoundedCharacterLabel {Q : ℕ} (p : Σ d : Fin Q, DirichletCharacter ℂ (d.val + 1)) :
    Σ d : ℕ, DirichletCharacter ℂ d :=
  ⟨p.1.val + 1, p.2⟩

/-- For a nonzero level bounded by the conductor cutoff, forgetting the bounded
primitive label gives the original conductor-character pair. The transport is
heterogeneously equal to its source. This identity certifies preservation of labels. -/
theorem forget_boundedPrimitiveCharacterLabel {q Q : ℕ} [NeZero q] (hq : q ≤ Q)
    (χ : DirichletCharacter ℂ q) :
    forgetBoundedCharacterLabel (boundedPrimitiveCharacterLabel hq χ) =
      primitiveCharacterLabel χ := by
  apply Sigma.ext (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr χ.conductor_ne_zero))
  exact cast_heq _ _

/-- At a fixed nonzero level below the conductor cutoff, bounded primitive labels
are injective. Forget the bound and use injectivity of unbounded primitive labels.
Thus embedding in the analytic family causes no duplicate-character loss. -/
theorem boundedPrimitiveCharacterLabel_injective {q Q : ℕ} [NeZero q] (hq : q ≤ Q) :
    Function.Injective (boundedPrimitiveCharacterLabel hq) := by
  intro χ ψ h
  apply primitiveCharacterLabel_injective q
  exact
    (forget_boundedPrimitiveCharacterLabel hq χ).symm.trans
      ((congrArg forgetBoundedCharacterLabel h).trans (forget_boundedPrimitiveCharacterLabel hq ψ))

/-- For a nonprincipal character at bounded nonzero level, its bounded label has
the original conductor and a primitive nonprincipal character. Transfer these
properties through the exact forgetting identity. They supply the family-ledger hypotheses. -/
theorem boundedPrimitiveCharacterLabel_properties {q Q : ℕ} [NeZero q] (hq : q ≤ Q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    (boundedPrimitiveCharacterLabel hq χ).1.val + 1 = χ.conductor ∧
      (boundedPrimitiveCharacterLabel hq χ).2.IsPrimitive ∧
      (boundedPrimitiveCharacterLabel hq χ).2 ≠ 1 := by
  have he := forget_boundedPrimitiveCharacterLabel hq χ
  have hprop :
    (fun p : (Σ d : ℕ, DirichletCharacter ℂ d) ↦ p.2.IsPrimitive ∧ p.2 ≠ 1)
      (forgetBoundedCharacterLabel (boundedPrimitiveCharacterLabel hq χ)) := by
    rw [he]
    exact ⟨χ.primitiveCharacter_isPrimitive, primitiveCharacter_ne_one_of_ne_one hne⟩
  exact ⟨congrArg Sigma.fst he, hprop⟩

open Classical in
/-- For a finite character family at bounded nonzero level, any additive weighted
sum over primitive labels equals the corresponding sum over bounded labels.
Use injectivity of both encodings and their forgetting identity. This preserves
all weights without an extra factor depending on the size of the family. -/
theorem sum_primitiveCharacterLabel_eq_bounded {q Q : ℕ} [NeZero q] (hq : q ≤ Q)
    (S : Finset (DirichletCharacter ℂ q)) {E : Type*} [AddCommMonoid E]
    (F : (Σ d : ℕ, DirichletCharacter ℂ d) → E) :
    ∑ p ∈ S.image primitiveCharacterLabel, F p =
      ∑ p ∈ S.image (boundedPrimitiveCharacterLabel hq), F (forgetBoundedCharacterLabel p) := by
  rw [Finset.sum_image (fun χ _ ψ _ h ↦ primitiveCharacterLabel_injective q h),
    Finset.sum_image (fun χ _ ψ _ h ↦ boundedPrimitiveCharacterLabel_injective hq h)]
  exact
    Finset.sum_congr rfl (fun χ _ ↦ congrArg F (forget_boundedPrimitiveCharacterLabel hq χ).symm)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
