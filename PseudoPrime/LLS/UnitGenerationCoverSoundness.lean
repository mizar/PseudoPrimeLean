/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.UnitGenerationProductSoundness
public import PseudoPrime.LLS.DivisorMaskSoundness

/-! # Subgroup transfer for divisor-covered LLS generation certificates

This proof layer transfers the executable product-and-divisor coverage check to subgroup
membership and an outside-prime witness. It trusts neither completeness of submitted divisors
nor a claimed unit-group order.

Keep this proof layer out of finite certificate imports. Changes to these proofs or unrelated
proof dependencies must not force the heavy finite checks to run again.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- A successful divisor-coverage check generates the entire unit group.
Input: a nonzero modulus, checked data and a subgroup containing eligible prime residues.
Claim: the subgroup is top. Proof: extract each unit bit and use closure under products.
Role: transfer finite certificates without an analytic bound or a separate depth assumption. -/
theorem subgroup_eq_top_of_unitCoverage {q cap depth code divisorCode : ℕ} [NeZero q]
    (hcheck : unitGenerationCoverCheck q cap depth code divisorCode = true) (H : Subgroup (ZMod q)ˣ)
    (hprime :
      ∀ p : ℕ, p.Prime → ¬p ∣ q → p ≤ cap → ∀ v : (ZMod q)ˣ, (v : ZMod q) = (p : ZMod q) → v ∈ H) :
    H = ⊤ := by
  have hb := Bool.and_eq_true_iff.mp hcheck
  have hc := Bool.and_eq_true_iff.mp hb.2
  have hrows := List.all_eq_true.mp hb.1
  apply (Subgroup.eq_top_iff' H).mpr
  intro u
  have hbit :=
    divisorCoverage_testBit hc.1 (of_decide_eq_true hc.2) (ZMod.val_lt (u : ZMod q))
      (ZMod.val_coe_unit_coprime u)
  exact
    mem_of_unitGenerationBit H (fun pd hpd ↦ unitGenerationRow_mem H hprime (hrows pd hpd)) u hbit

/-- A checked divisor-covered certificate supplies an outside prime below the integer cap.
Input: a nonzero modulus, successful check and a proper subgroup of the unit group.
Claim: an eligible prime through the cap has no representative in that subgroup.
Proof: absence would make generation force the subgroup to be top.
Role: the finite algebraic input to the LLS analytic transfer. -/
theorem exists_prime_outside_of_unitCoverage {q cap depth code divisorCode : ℕ} [NeZero q]
    (hcheck : unitGenerationCoverCheck q cap depth code divisorCode = true) (H : Subgroup (ZMod q)ˣ)
    (hH : H ≠ ⊤) : ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ p ≤ cap ∧ ¬∃ v ∈ H, (v : ZMod q) = (p : ZMod q) := by
  by_contra hnone
  refine hH (subgroup_eq_top_of_unitCoverage hcheck H ?_)
  intro p hp hd hb u hu
  have hex : ∃ v ∈ H, (v : ZMod q) = (p : ZMod q) :=
    Classical.byContradiction (fun hh ↦ hnone ⟨p, hp, hd, hb, hh⟩)
  obtain ⟨v, hv, hev⟩ := hex
  exact (Units.ext (hev.trans hu.symm)) ▸ hv

end PseudoPrime.LLS
