/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! Annihilators and orthogonality for subgroups of units modulo a natural number. -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Characters in the annihilator `H̃`: their values are one on every unit in `H`.
This supplies the character hypothesis in Lemma 6.1 without assuming quadraticity. -/
def annihilatesSubgroup {q : ℕ} (χ : DirichletCharacter ℂ q) (H : Subgroup (ZMod q)ˣ) : Prop :=
  ∀ u : (ZMod q)ˣ, u ∈ H → χ (u : ZMod q) = 1

/-- The finite subgroup of complex characters equal to one on every unit of `H`.
It is the dual subgroup supplied by finite character duality, used to average the
smoothed Mangoldt sums in Proposition 6.1. -/
noncomputable def subgroupAnnihilator {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ) :
    Subgroup (DirichletCharacter ℂ q) :=
  (MulChar.subgroupOrderIsoSubgroupMulChar (ZMod q) ℂ H).ofDual

variable {q : ℕ} [NeZero q]

/-- Enumerate the finite annihilator for sums over its characters. Finiteness follows
from finite character duality; no choice of a particular list affects the sums. -/
noncomputable instance subgroupAnnihilatorFintype (H : Subgroup (ZMod q)ˣ) :
    Fintype (subgroupAnnihilator H) :=
  Fintype.ofFinite _

/-- Membership in the dual subgroup means precisely that the character annihilates `H`.
The finite-duality membership formula identifies the two definitions, allowing the
characters in these sums to satisfy the hypothesis of Lemma 6.1. -/
theorem mem_subgroupAnnihilator_iff (H : Subgroup (ZMod q)ˣ) (χ : DirichletCharacter ℂ q) :
    χ ∈ subgroupAnnihilator H ↔ annihilatesSubgroup χ H := by
  exact MulChar.mem_subgroupOrderIsoSubgroupMulChar_iff

/-- The annihilator of the identity subgroup contains every complex character.
Each unit in the identity subgroup is one, where a character takes value one.
This identifies residue-class averages with full-character averages. -/
theorem subgroupAnnihilator_bot : subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ) = ⊤ := by
  apply eq_top_iff.mpr
  intro χ _
  apply (mem_subgroupAnnihilator_iff ⊥ χ).mpr
  intro u hu
  rw [Subgroup.mem_bot.mp hu, Units.val_one, χ.map_one]

/-- Summing over the identity subgroup's annihilator equals summing over all characters.
The subtype projection is a bijection because its subgroup is the full character group.
Transport the finite sum through that projection.
This applies to any additive commutative monoid. -/
theorem sum_subgroupAnnihilator_bot {R : Type*} [AddCommMonoid R] (f : DirichletCharacter ℂ q → R) :
    (∑ χ : subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ), f χ.val) =
      ∑ χ : DirichletCharacter ℂ q, f χ := by
  have hs :
    Function.Surjective
      (Subtype.val : subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ) → DirichletCharacter ℂ q) := by
    intro χ
    refine ⟨⟨χ, ?_⟩, rfl⟩
    rw [subgroupAnnihilator_bot]
    exact Subgroup.mem_top χ
  exact Fintype.sum_bijective Subtype.val ⟨Subtype.val_injective, hs⟩ _ _ (fun _ ↦ rfl)

open Classical in
/-- Removing the principal character from the identity annihilator gives the
same finite sum as removing it from the full character group.
Express each erased sum as the total sum minus the principal value and use the full-sum identity.
This connects parity averages to the nonprincipal sums in residue-class criteria. -/
theorem sum_nonprincipal_subgroupAnnihilator_bot {R : Type*} [AddCommGroup R]
    (f : DirichletCharacter ℂ q → R) :
    (∑ χ ∈ Finset.univ.erase (1 : subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ)), f χ.val) =
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), f χ := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ (1 : subgroupAnnihilator (⊥ : Subgroup (ZMod q)ˣ))),
    Finset.sum_erase_eq_sub (Finset.mem_univ (1 : DirichletCharacter ℂ q)),
    sum_subgroupAnnihilator_bot f, Subgroup.coe_one]

/-- The annihilator has exactly `H.index` characters. Finite duality identifies its
cardinality with that of the quotient of units. This counts the principal and
nonprincipal contributions in the averaged estimate. -/
theorem card_subgroupAnnihilator (H : Subgroup (ZMod q)ˣ) :
    Fintype.card (subgroupAnnihilator H) = H.index := by
  rw [← Nat.card_eq_fintype_card, Subgroup.index_eq_card]
  exact MulChar.card_subgroupOrderIsoSubgroupMulChar

/-- A unit belongs to `H` exactly when every character of its annihilator is one there.
Apply the inverse finite-duality membership formula and the order-isomorphism identity.
This separates any residue outside the subgroup. -/
theorem mem_iff_subgroupAnnihilator (H : Subgroup (ZMod q)ˣ) (u : (ZMod q)ˣ) :
    u ∈ H ↔ ∀ χ ∈ subgroupAnnihilator H, χ (u : ZMod q) = 1 := by
  have h :=
    MulChar.mem_subgroupOrderIsoSubgroupMulChar_symm_iff (X := subgroupAnnihilator H) (m := u)
  simpa only [subgroupAnnihilator, OrderDual.toDual_ofDual, OrderIso.symm_apply_apply] using h

/-- A unit outside `H` is separated from one by a character in the annihilator.
The double-annihilator identity gives the witness by contradiction. This character
forces cancellation in the orthogonality sum. -/
theorem exists_subgroupAnnihilator_apply_ne_one (H : Subgroup (ZMod q)ˣ) {u : (ZMod q)ˣ}
    (hu : u ∉ H) : ∃ χ : subgroupAnnihilator H, χ.val (u : ZMod q) ≠ 1 := by
  by_contra h
  apply hu
  apply (mem_iff_subgroupAnnihilator H u).mpr
  intro χ hχ
  exact Classical.byContradiction (fun hn ↦ h ⟨⟨χ, hχ⟩, hn⟩)

/-- The annihilator character sum vanishes at every unit outside `H`.
Multiply by a separating character and permute the finite character group; its
nonzero scalar difference forces the sum to be zero. This is the cancellation
clause of the subgroup orthogonality relation. -/
theorem sum_subgroupAnnihilator_eq_zero (H : Subgroup (ZMod q)ˣ) {u : (ZMod q)ˣ} (hu : u ∉ H) :
    ∑ χ : subgroupAnnihilator H, χ.val (u : ZMod q) = 0 := by
  obtain ⟨χ, hχ⟩ := exists_subgroupAnnihilator_apply_ne_one H hu
  apply eq_zero_of_mul_eq_self_left hχ
  rw [Finset.mul_sum]
  exact
    Fintype.sum_bijective (fun ψ : subgroupAnnihilator H ↦ χ * ψ) (Group.mulLeft_bijective χ) _ _
      (fun ψ ↦ (MulChar.mul_apply χ.val ψ.val u).symm)

/-- On every unit of `H`, the annihilator character sum equals `H.index`.
All summands are one, and finite duality supplies their number. Together with
cancellation outside `H`, this is the subgroup orthogonality formula. -/
theorem sum_subgroupAnnihilator_eq_index (H : Subgroup (ZMod q)ˣ) {u : (ZMod q)ˣ} (hu : u ∈ H) :
    ∑ χ : subgroupAnnihilator H, χ.val (u : ZMod q) = (H.index : ℂ) := by
  calc
    _ = ∑ _ : subgroupAnnihilator H, (1 : ℂ) :=
      Finset.sum_congr rfl (fun χ _ ↦ (mem_subgroupAnnihilator_iff H χ.val).mp χ.property u hu)
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_subgroupAnnihilator]

end PseudoPrime.NumberTheory
