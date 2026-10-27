/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Part1ProductCertificates

/-! # Shared unit-witness conversion and product checks at moduli three through five -/

@[expose] public section

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

/-- Input: a small modulus. Definition: product codes 130,131,258 for moduli three,four,five.
Output: an integer code. Role: certify these three unit groups with prime cap five. -/
def retainedSavingSmallCode (q : ℕ) : ℕ :=
  if q = 3 then 130 else if q = 4 then 131 else 258

/-- Claim: every modulus between three and five passes its finite product check.
Proof: kernel arithmetic over Fin 6. Role: cover the small exceptions to the uniform cap 19. -/
theorem retained_saving_small_product_check :
    ∀ q : Fin 6,
      3 ≤ q.val →
        NumberTheory.generationProductCheck q.val 5 (q.val.log2 + 1)
            (retainedSavingSmallCode q.val) =
          true := by
  decide +kernel

end PseudoPrime.LLS
