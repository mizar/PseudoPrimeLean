/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PreciseSavingSmallBounds
public import PseudoPrime.LLS.Part1RetainedSavingProductBounds
public import PseudoPrime.LLS.Part1FromThree
public import PseudoPrime.LLS.CharacterPart2FromFive

/-! # Precise reciprocal-saving Part 1 witnesses from modulus three -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: a modulus between five and 2999, a proper subgroup, and a cap covering the catalog cap.
Claim: a coprime outside prime exists below that cap.
Proof: locate the existing checked product block and transfer its prime bound.
Role: reuse the finite catalog for any later real radius without repeating its index proof. -/
theorem exists_prime_outside_catalog_of_cap {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hQ : q < 3000)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) {R : ℝ} (hcap : (llsPart1FinitePrimeCap q : ℝ) ≤ R) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ R := by
  let r := q - 5
  have hs : r + 5 = q := Nat.sub_add_cancel hq
  have hb : r / 128 < 24 :=
    (Nat.div_lt_iff_lt_mul (by decide +kernel : 0 < 128)).mpr (by linarith only [hs, hQ])
  have hi : r % 128 < 128 := Nat.mod_lt r (by decide +kernel : 0 < 128)
  have he : 5 + 128 * (r / 128) + r % 128 = q := by
    have hd := Nat.mod_add_div r 128
    linarith only [hd, hs]
  have hcheck :=
    lls_part1_product_block_sound (SmallPart1.part1_catalog_checks ⟨r / 128, hb⟩) hi
      (show 5 + 128 * (r / 128) + r % 128 < 3000 by
        rw [he]; exact hQ)
  rw [he] at hcheck
  obtain ⟨p, hp, hd, hbound, hout⟩ :=
    NumberTheory.exists_prime_outside_of_generationProductCheck hcheck
      (modulus_le_product_depth (NeZero.ne q)) H hH
  exact
    ⟨p, primeOutsideSubgroup_of_image_exclusion H hp hd hout, (Nat.cast_le.mpr hbound).trans hcap⟩

/-- Input: a modulus at least six.
Claim: its finite catalog prime cap lies inside the precise-saving squared radius.
Proof: use the new bounds nineteen and forty-three on the two catalog ranges.
Role: reuse all finite certificate data unchanged. -/
theorem precise_saving_finite_cap_le_radius {q : ℕ} (hq : 6 ≤ q) :
    (llsPart1FinitePrimeCap q : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  by_cases h : q < 705
  · simpa only [llsPart1FinitePrimeCap, ite_eq_left h, Nat.cast_ofNat] using
      precise_saving_radius_sq_ge_nineteen hq
  · simpa only [llsPart1FinitePrimeCap, ite_eq_right h, Nat.cast_ofNat] using
      precise_saving_radius_sq_ge_forty_three (Nat.le_of_not_gt h)

/-- Input: a modulus between three and five and a proper unit subgroup.
Claim: a coprime outside prime exists within the precise-saving radius.
Proof: reuse the checked small product codes and the new radius lower bound five.
Role: handle the three smallest nonvacuous moduli. -/
theorem exists_prime_outside_preciseSaving_small {q : ℕ} [NeZero q] (hq : 3 ≤ q) (hQ : q ≤ 5)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  have hc := retained_saving_small_product_check ⟨q, Nat.lt_succ_iff.mpr hQ⟩ hq
  obtain ⟨p, hp, hd, hb, hout⟩ :=
    NumberTheory.exists_prime_outside_of_generationProductCheck hc
      (modulus_le_product_depth (NeZero.ne q)) H hH
  exact
    ⟨p, primeOutsideSubgroup_of_image_exclusion H hp hd hout,
      (Nat.cast_le.mpr hb).trans (precise_saving_radius_sq_ge_five_three_five hq hQ)⟩

/-- Input: GRH, a modulus at least three, and a proper unit subgroup.
Claim: a coprime outside prime exists within the precise-saving squared radius.
Proof: combine the established analytic theorem with unchanged small and catalog certificates.
Role: expose the full-range improvement without generating new finite data. -/
theorem exists_prime_outside_preciseSaving_from_three
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {q : ℕ} [NeZero q] (hq : 3 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤) :
    ∃ p : ℕ, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  by_cases hlarge : 3000 ≤ q
  · obtain ⟨p, hp, hd, hb, hout⟩ :=
      exists_prime_outside_subgroup_le_preciseSavingRadius hlarge H hH hGRH
    exact ⟨p, primeOutsideSubgroup_of_image_exclusion H hp hd hout, hb⟩
  · by_cases hsmall : q ≤ 5
    · exact exists_prime_outside_preciseSaving_small hq hsmall H hH
    · exact
        exists_prime_outside_catalog_of_cap
          (le_trans (by norm_num only : (5 : ℕ) ≤ 6) (Nat.lt_of_not_ge hsmall))
          (Nat.lt_of_not_ge hlarge) H hH
          (precise_saving_finite_cap_le_radius (Nat.lt_of_not_ge hsmall))

/-- Input: GRH, a nonprincipal complex character, and a modulus at least three.
Claim: a coprime non-one prime exists through the precise-saving squared radius.
Proof: apply the subgroup theorem to the proper kernel of the character on units.
Role: provide the full-range character counterpart of the strengthened Part 1 bound. -/
theorem exists_prime_character_ne_one_le_preciseSavingRadius_from_three {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (hq : 3 ≤ q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ, p.Prime ∧ ¬p ∣ q ∧ χ p ≠ 1 ∧ (p : ℝ) ≤ (preciseSavingRadiusRoot q) ^ 2 := by
  obtain ⟨p, ⟨hp, hd, u, hu, heq⟩, hb⟩ :=
    exists_prime_outside_preciseSaving_from_three hGRH hq χ.toUnitHom.ker
      (character_unit_kernel_ne_top χ hne)
  refine ⟨p, hp, hd, ?_, hb⟩
  intro h
  apply hu
  apply MonoidHom.mem_ker.mpr
  apply Units.ext
  simpa only [MulChar.coe_toUnitHom, Units.val_one, heq] using h

end PseudoPrime.LLS
