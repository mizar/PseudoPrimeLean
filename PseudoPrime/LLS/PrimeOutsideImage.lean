/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Prime witnesses outside subgroup images -/

public section

namespace PseudoPrime.LLS

/-- Input: a prime not dividing q and exclusion of its residue from the subgroup image.
Claim: it satisfies the unit-witness predicate PrimeOutsideSubgroup.
Proof: construct its canonical unit and use the image exclusion.
Role: share the algebraic witness conversion across analytic radius bounds. -/
theorem primeOutsideSubgroup_of_image_exclusion {q p : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hp : p.Prime) (hd : ¬p ∣ q) (hout : ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q)) :
    PrimeOutsideSubgroup q H p := by
  let u := ZMod.unitOfCoprime p (hp.coprime_iff_not_dvd.mpr hd)
  have hu : (u : ZMod q) = (p : ZMod q) := ZMod.coe_unitOfCoprime _ _
  exact ⟨hp, hd, u, fun h ↦ hout ⟨u, h, hu⟩, hu⟩

end PseudoPrime.LLS
