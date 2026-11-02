/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationProductCheck
public import PseudoPrime.LLS.UnitGenerationCheckSoundness
public import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Soundness of finite LLS product certificates

This proof layer establishes bit support, bounded coverage, and subgroup representatives for
LLS's mixed-radix products. The coverage-check soundness module uses these algebraic lemmas
to obtain subgroup generation and an outside-prime witness.

Finite certificate blocks should import the computational checker instead of this proof layer.
Otherwise additions or changes to unrelated proofs, declarations, or dependencies here can
invalidate those finite proofs and force expensive kernel rechecking. Preserve the direction
from soundness to computation and keep analytic interfaces outside the computational entry.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- A set bit in a bounded union comes from a leaf below its exclusive bound.
Input: a true bit test at arbitrary depth and start.
Claim: some eligible leaf has that bit; induction discards empty subtrees and splits unions.
Role: extract a concrete mixed-radix product from the coverage checker. -/
theorem unitGenerationBoundedOr_support {bound depth start r : ℕ} {f : ℕ → ℕ}
    (h : (unitGenerationBoundedOr bound f depth start).testBit r = true) :
    ∃ i : ℕ, i < bound ∧ (f i).testBit r = true := by
  induction depth generalizing start
  case zero =>
    by_cases hs : start < bound
    · rw [unitGenerationBoundedOr, ite_eq_left hs] at h
      exact ⟨start, hs, h⟩
    · rw [unitGenerationBoundedOr, ite_eq_right hs, Nat.zero_testBit] at h
      exact Bool.noConfusion h
  case succ depth ih =>
    by_cases hs : bound ≤ start
    · rw [unitGenerationBoundedOr, ite_eq_left hs, Nat.zero_testBit] at h
      exact Bool.noConfusion h
    · rw [unitGenerationBoundedOr, ite_eq_right hs, Nat.testBit_lor, Bool.or_eq_true] at h
      exact h.elim ih ih

/-- Every eligible leaf bit appears in a bounded union covering that leaf.
Input: interval bounds, an index below the exclusive bound and a true leaf bit.
Claim: the union bit is true; induction selects the half containing the index.
Role: supply each coprime residue to the exact unit mask. -/
theorem unitGenerationBoundedOr_cover {bound depth start i r : ℕ} {f : ℕ → ℕ} (hl : start ≤ i)
    (hu : i < start + 2 ^ depth) (hi : i < bound) (h : (f i).testBit r = true) :
    (unitGenerationBoundedOr bound f depth start).testBit r = true := by
  induction depth generalizing start
  case zero =>
    have he : i = start := Nat.le_antisymm (Nat.le_of_lt_succ hu) hl
    rw [← he, unitGenerationBoundedOr, ite_eq_left hi]
    exact h
  case succ depth ih =>
    have hs : ¬bound ≤ start := Nat.not_le_of_lt (hl.trans_lt hi)
    rw [unitGenerationBoundedOr, ite_eq_right hs, Nat.testBit_lor, Bool.or_eq_true]
    by_cases hm : i < start + 2 ^ depth
    · exact Or.inl (ih hl hm)
    · rw [Nat.pow_succ, Nat.mul_two, ← Nat.add_assoc] at hu
      exact Or.inr (ih (Nat.le_of_not_gt hm) hu)

/-- Products of represented generators remain represented inside the subgroup.
Input: a subgroup, generator/radix rows with subgroup representatives, and an index.
Claim: the mixed-radix product has a subgroup representative.
Proof: induction on rows and subgroup closure. Role: transfer exact bit coverage to generation. -/
theorem unitGenerationProductValue_mem {q : ℕ} (H : Subgroup (ZMod q)ˣ) {rows : List (ℕ × ℕ)}
    (hrows : ∀ pd ∈ rows, ∃ v ∈ H, (v : ZMod q) = (pd.1 : ZMod q)) (i : ℕ) :
    ∃ v ∈ H, (v : ZMod q) = unitGenerationProductValue q rows i := by
  induction rows generalizing i
  case nil => exact ⟨1, H.one_mem, rfl⟩
  case cons pd rows ih =>
    obtain ⟨v, hv, he⟩ := hrows pd List.mem_cons_self
    obtain ⟨u, hu, heu⟩ := ih (fun r hr ↦ hrows r (List.mem_cons_of_mem pd hr)) (i / pd.2)
    refine ⟨u * v ^ (i % pd.2), H.mul_mem hu (H.pow_mem hv _), ?_⟩
    simp only [unitGenerationProductValue, Units.val_mul, Units.val_pow_eq_pow_val, heu, he]

/-- An eligible checked row has a representative in a subgroup containing eligible primes.
Input: the subgroup's prime closure and the row's label, nondivisibility and cap guards.
Claim: a subgroup unit represents the row's generator.
Proof: certify its prime label and construct the coprime unit. Role: validate all product rows. -/
theorem unitGenerationRow_mem {q cap : ℕ} (H : Subgroup (ZMod q)ˣ)
    (hprime :
      ∀ p : ℕ, p.Prime → ¬p ∣ q → p ≤ cap → ∀ v : (ZMod q)ˣ, (v : ZMod q) = (p : ZMod q) → v ∈ H)
    {pd : ℕ × ℕ}
    (h : (unitGenerationPrimes.contains pd.1 && decide (¬pd.1 ∣ q) && decide (pd.1 ≤ cap)) = true) :
    ∃ v ∈ H, (v : ZMod q) = (pd.1 : ZMod q) := by
  have hs := Bool.and_eq_true_iff.mp h
  have ht := Bool.and_eq_true_iff.mp hs.1
  have hp := prime_of_mem_unitGenerationPrimes (List.contains_iff_mem.mp ht.1)
  have hd := of_decide_eq_true ht.2
  let v := ZMod.unitOfCoprime pd.1 (hp.coprime_iff_not_dvd.mpr hd)
  have hv : (v : ZMod q) = (pd.1 : ZMod q) := ZMod.coe_unitOfCoprime _ _
  exact ⟨v, hprime pd.1 hp hd (of_decide_eq_true hs.2) v hv, hv⟩

/-- A unit with a represented product bit belongs to any subgroup containing the row generators.
Input: a subgroup, row representatives, a unit and its product-mask bit.
Claim: the unit is in the subgroup. Proof: extract the product and identify unit representatives.
Role: share subgroup transfer across exact-unit and divisor-mask coverage checks. -/
theorem mem_of_unitGenerationBit {q depth : ℕ} [NeZero q] {rows : List (ℕ × ℕ)}
    (H : Subgroup (ZMod q)ˣ) (hrows : ∀ pd ∈ rows, ∃ v ∈ H, (v : ZMod q) = (pd.1 : ZMod q))
    (u : (ZMod q)ˣ)
    (hm : (unitGenerationProductMask q depth rows).testBit (u : ZMod q).val = true) : u ∈ H := by
  obtain ⟨i, _, hi⟩ := unitGenerationBoundedOr_support hm
  rw [Nat.testBit_two_pow] at hi
  have he := congrArg (fun j : ℕ ↦ (j : ZMod q)) (of_decide_eq_true hi)
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at he
  obtain ⟨v, hv, hev⟩ := unitGenerationProductValue_mem H hrows i
  exact (Units.ext (hev.trans he)) ▸ hv

end PseudoPrime.LLS
