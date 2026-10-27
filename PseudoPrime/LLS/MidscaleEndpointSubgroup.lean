/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.MidscaleEndpointRadius
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Proper subgroup witnesses from the midscale endpoint radius -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH on the certified midscale interval, every proper unit subgroup
has a prime outside its image through the squared affine radius. Pull back a
nonprincipal quotient character and apply the original-level character bound.
Nonunit primes are permitted by this subgroup-image formulation. -/
theorem exists_prime_outside_subgroup_le_midscale_radius_sq {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hlo : 1339 / 50 ≤ Real.log q)
    (hhi : Real.log q ≤ 26269 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (midscaleEndpointRadius (Real.log q)) ^ 2 ∧
        ¬∃ u ∈ H, (u : ZMod q) = (p : ZMod q) := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨z, hz⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχ⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hz
  obtain ⟨p, hp, hb, hv⟩ :=
    exists_prime_ne_one_le_midscale_radius_sq (pullbackCharacter χ')
      (pullbackCharacter_ne_one_of_ne_one χ' hχ) hGRH hlo hhi
  refine ⟨p, hp, hb, ?_⟩
  rintro ⟨u, hu, he⟩
  apply hv
  rw [← he]
  exact pullbackCharacter_eq_one_of_mem χ' hu

end PseudoPrime.LLS.PaperStatements
