/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitGenerationBalanced
public import PseudoPrime.LLS.ParityRationalWitnessProfiles
public import PseudoPrime.Analysis.LLSSmallModulusGenerationBounds

/-! # Transferring finite generation certificates to the parity profile

Proper subgroups omit an eligible prime from every valid generation tree.
The analytic profile exceeds seven for q ≥ 3 and eighty-one for q ≥ 8,
so uniform integer caps suffice for the finite small-modulus extension.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Use cap seven below modulus eight and cap eighty-one otherwise.
The cap is independent of factorization and the certificate search algorithm.
It is bounded by the parity profile for every modulus at least three. -/
def smallModulusPrimeCap (q : ℕ) : ℕ :=
  if q < 8 then 7 else 81

/-- For q ≥ 3, the selected integer cap lies below the parity profile.
Split at modulus eight and apply the corresponding positive-root square comparison.
This transfers finite integer witness bounds to the public analytic formula. -/
theorem smallModulusPrimeCap_le_parity_square {q : ℕ} (hq : 3 ≤ q) :
    (smallModulusPrimeCap q : ℝ) ≤
      (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  by_cases h8 : q < 8
  · simpa only [smallModulusPrimeCap, ite_eq_left h8, Nat.cast_ofNat] using
      Analysis.parity_square_ge_seven hq
  · simpa only [smallModulusPrimeCap, ite_eq_right h8, Nat.cast_ofNat] using
      Analysis.parity_square_ge_eighty_one (Nat.le_of_not_gt h8)

/-- For q ≥ 3 with a valid tree at the selected cap, every proper subgroup has an outside prime
through the parity profile. Transfer the integer witness using the cap comparison.
This is the small-modulus consumer for the finite certificate catalog. -/
theorem exists_prime_outside_le_parity_of_generation_tree {q : ℕ} [NeZero q]
    {tree : ℕ → NumberTheory.UnitGenerationNode} (hq : 3 ≤ q)
    (hvalid : NumberTheory.UnitGenerationTreeValid q (smallModulusPrimeCap q) tree)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (42589 / 7000 : ℝ) * Real.log (Real.log q) + 77 / 25) ^ 2 := by
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_of_generation_tree hvalid H hH
  exact ⟨p, hp, (Nat.cast_le.mpr hb).trans (smallModulusPrimeCap_le_parity_square hq)⟩

end PseudoPrime.LLS
