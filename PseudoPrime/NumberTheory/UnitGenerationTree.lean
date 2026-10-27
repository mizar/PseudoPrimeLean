/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Nat.Prime.Basic

/-! # Checked prime-generation trees for finite unit groups

Every nonidentity unit has a prime-labelled parent edge of smaller natural depth.
Finite validation and strong induction show that any subgroup containing the
eligible primes is the whole unit group.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A node in a prime-labelled unit-generation tree. The parent and prime
encode a modular multiplication edge; the depth supplies a well-founded order.
Validation checks the bounds, unit conditions and strict depth decrease.
This data is independent of analytic bounds and certificate generation algorithms. -/
structure UnitGenerationNode where
  /-- Parent residue representative. -/
  parent : ℕ
  /-- Prime used to obtain this residue from its parent. -/
  prime : ℕ
  /-- Natural depth, strictly larger than the parent's depth at nonroot units. -/
  depth : ℕ

/-- Validation at modulus q and integer cap: each coprime representative
is one or has a unit parent, smaller parent depth, eligible prime label and
correct multiplication remainder. Nonunit representatives impose no condition.
These invariants imply generation of the entire unit group. -/
def UnitGenerationTreeValid (q cap : ℕ) (tree : ℕ → UnitGenerationNode) : Prop :=
  ∀ r : Fin q,
    Nat.Coprime r.val q →
      r.val = 1 ∨
        (tree r.val).parent < q ∧
          Nat.Coprime (tree r.val).parent q ∧
          (tree (tree r.val).parent).depth < (tree r.val).depth ∧
          (tree r.val).prime.Prime ∧
          ¬(tree r.val).prime ∣ q ∧
          (tree r.val).prime ≤ cap ∧ ((tree r.val).parent * (tree r.val).prime) % q = r.val

/-- The validity predicate is decidable because it quantifies over Fin q
and uses decidable natural-number arithmetic. This instance makes the checker executable. -/
instance (q cap : ℕ) (tree : ℕ → UnitGenerationNode) :
    Decidable (UnitGenerationTreeValid q cap tree) := by
  unfold UnitGenerationTreeValid
  infer_instance

/-- The computable Boolean reflection of the finite generation-tree validity
predicate at q and cap. It checks all residue representatives in Fin q.
A true result is transferred to mathematical validity by the soundness theorem. -/
def unitGenerationTreeCheck (q cap : ℕ) (tree : ℕ → UnitGenerationNode) : Bool :=
  decide (UnitGenerationTreeValid q cap tree)

/-- A true finite check implies the generation-tree invariants.
Reflect the decidable finite predicate. This separates executable checking
from the subgroup-generation soundness theorem. -/
theorem unitGenerationTreeCheck_sound {q cap : ℕ} {tree : ℕ → UnitGenerationNode}
    (h : unitGenerationTreeCheck q cap tree = true) : UnitGenerationTreeValid q cap tree :=
  of_decide_eq_true h

/-- Decode a packed array into tree nodes. A word stores parent*1024,
prime*8 and depth, with prime and depth decoded modulo 128 and 8.
Missing entries decode to zero; validation must still cover every unit residue.
This compact data interface is used by deterministic finite certificate generators. -/
def unitGenerationTreeOfPacked (entries : Array ℕ) (r : ℕ) : UnitGenerationNode :=
  let word := entries.getD r 0;
  ⟨word / 1024, word / 8 % 128, word % 8⟩

/-- For nonzero q and a valid tree, a subgroup containing every eligible
prime through cap contains every unit representing a coprime residue below q.
Induct strongly on the node depth and combine the parent with its prime label.
This is the pointwise generation argument used to prove the subgroup is top. -/
theorem unit_mem_of_valid_generation_tree {q cap : ℕ} [NeZero q] {tree : ℕ → UnitGenerationNode}
    (hvalid : UnitGenerationTreeValid q cap tree) (H : Subgroup (ZMod q)ˣ)
    (hprime :
      ∀ p : ℕ, p.Prime → ¬p ∣ q → p ≤ cap → ∀ u : (ZMod q)ˣ, (u : ZMod q) = (p : ZMod q) → u ∈ H)
    {r : ℕ} (hr : r < q) (hc : Nat.Coprime r q) :
    ∀ u : (ZMod q)ˣ, (u : ZMod q) = (r : ZMod q) → u ∈ H := by
  have hs :
    ∀ d : ℕ,
      ∀ r : ℕ,
        (tree r).depth = d →
          r < q → Nat.Coprime r q → ∀ u : (ZMod q)ˣ, (u : ZMod q) = (r : ZMod q) → u ∈ H := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hd hr hc u hu
      rcases hvalid ⟨r, hr⟩ hc with he | ⟨hp, hcp, hdep, hpprime, hpdiv, hpcap, hmod⟩
      · change r = 1 at he
        have hue : u = 1 := Units.ext (by simpa only [he, Nat.cast_one, Units.val_one] using hu)
        exact hue ▸ H.one_mem
      · have hv := (ZMod.isUnit_iff_coprime (tree r).parent q).mpr hcp
        have hw :=
          (ZMod.isUnit_iff_coprime (tree r).prime q).mpr (hpprime.coprime_iff_not_dvd.mpr hpdiv)
        have hmparent :=
          ih (tree (tree r).parent).depth (hd ▸ hdep) (tree r).parent rfl hp hcp hv.unit
            (IsUnit.unit_spec hv)
        have hmprime := hprime (tree r).prime hpprime hpdiv hpcap hw.unit (IsUnit.unit_spec hw)
        have heq : u = hv.unit * hw.unit := by
          apply Units.ext
          rw [hu, Units.val_mul, IsUnit.unit_spec hv, IsUnit.unit_spec hw]
          have ht := congrArg (fun n : ℕ ↦ (n : ZMod q)) hmod
          simpa only [ZMod.natCast_mod, Nat.cast_mul] using ht.symm
        exact heq ▸ H.mul_mem hmparent hmprime
  exact hs (tree r).depth r rfl hr hc

/-- For nonzero q, a valid tree and a subgroup containing all eligible
prime residues through cap, the subgroup equals top. Represent each unit by
its natural residue and apply the depth induction theorem.
This is the algebraic soundness interface for small-modulus prime bounds. -/
theorem subgroup_eq_top_of_valid_generation_tree {q cap : ℕ} [NeZero q]
    {tree : ℕ → UnitGenerationNode} (hvalid : UnitGenerationTreeValid q cap tree)
    (H : Subgroup (ZMod q)ˣ)
    (hprime :
      ∀ p : ℕ, p.Prime → ¬p ∣ q → p ≤ cap → ∀ u : (ZMod q)ˣ, (u : ZMod q) = (p : ZMod q) → u ∈ H) :
    H = ⊤ := by
  apply (Subgroup.eq_top_iff' H).mpr
  intro u
  have hv := ZMod.natCast_zmod_val (u : ZMod q)
  have hc : Nat.Coprime (u : ZMod q).val q := by
    apply (ZMod.isUnit_iff_coprime (u : ZMod q).val q).mp
    rw [hv]
    exact u.isUnit
  exact unit_mem_of_valid_generation_tree hvalid H hprime (ZMod.val_lt (u : ZMod q)) hc u hv.symm

end PseudoPrime.NumberTheory
