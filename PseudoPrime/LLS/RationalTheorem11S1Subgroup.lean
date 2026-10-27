/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RationalTheorem11S1
public import PseudoPrime.LLS.Theorem11S1Subgroup

/-! # Rational Part 1 subgroup and least-prime witnesses -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, q ≥ 3000 and H proper, a coprime prime outside H lies
through the factor-sensitive rational Part 1 radius squared.
Pull back a nonprincipal quotient character and apply its rational-radius witness.
This is the proper-subgroup form of the smaller additive correction. -/
theorem exists_prime_outside_subgroup_le_rationalRadius {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p, PrimeOutsideSubgroup q H p ∧ (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 := by
  have : H.Normal := H.normal_of_isMulCommutative
  have : Nontrivial ((ZMod q)ˣ ⧸ H) := QuotientGroup.nontrivial_iff.mpr hH
  obtain ⟨x, hx1⟩ := exists_ne (1 : (ZMod q)ˣ ⧸ H)
  obtain ⟨χ', hχx⟩ := MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity ((ZMod q)ˣ ⧸ H) ℂ hx1
  obtain ⟨p, hp, hd, hv, hb⟩ :=
    exists_prime_character_ne_one_le_rationalRadius (pullbackCharacter χ') hq
      (pullbackCharacter_ne_one_of_ne_one χ' hχx) hGRH
  have hc : Nat.Coprime p q := hp.coprime_iff_not_dvd.mpr hd
  have hu : IsUnit (p : ZMod q) := (ZMod.isUnit_iff_coprime p q).mpr hc
  refine ⟨p, ⟨hp, hd, hu.unit, ?_, IsUnit.unit_spec hu⟩, hb⟩
  intro hm
  apply hv
  have he := pullbackCharacter_eq_one_of_mem χ' (H := H) hm
  rwa [IsUnit.unit_spec hu] at he

/-- Under GRH, q ≥ 3000 and H proper, the least coprime outside prime is
at most the rational Part 1 radius squared. Minimize the bounded existence witness.
Minimality is among all eligible primes and retains the pointwise expression. -/
theorem exists_least_prime_outside_subgroup_le_rationalRadius {q : ℕ} [NeZero q] (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (rationalRadiusRoot q) ^ 2 ∧ ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_rationalRadius hq H hH hGRH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

/-- Under GRH, q ≥ 3000 and H proper, a coprime outside prime lies through
(log q+(1791/250)log log q+499/250)². Bound the nonnegative rational-radius root.
This realizes the universal rational triple at the same starting value. -/
theorem exists_prime_outside_subgroup_le_rationalProfile3000 {q : ℕ} (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250) ^ 2 := by
  have hq0 : q ≠ 0 := Nat.ne_zero_of_lt ((by decide : (0 : ℕ) < 3000).trans_le hq)
  let : NeZero q := ⟨hq0⟩
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_rationalRadius hq H hH hGRH
  have hR := rationalRadiusRoot_le_logarithmic_shift hq
  have hR0 : 0 ≤ rationalRadiusRoot q := by
    unfold rationalRadiusRoot
    have hL := Analysis.eight_lt_log_level hq
    have hB : 0 ≤ rationalCorrectionTerm q := le_max_left _ _
    linarith only [hL, hB]
  exact ⟨p, hp, hb.trans ((sq_le_sq₀ hR0 (hR0.trans hR)).mpr hR)⟩

/-- Under GRH, q ≥ 3000 and H proper, the least coprime outside prime is
at most (log q+(1791/250)log log q+499/250)². Minimize the bounded subgroup witness.
This preserves the rational triple and starting value in the least-prime interface. -/
theorem exists_least_prime_outside_subgroup_le_rationalProfile3000 {q : ℕ} (hq : 3000 ≤ q)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      PrimeOutsideSubgroup q H p ∧
        (p : ℝ) ≤ (Real.log q + (1791 / 250 : ℝ) * Real.log (Real.log q) + 499 / 250) ^ 2 ∧
        ∀ r, PrimeOutsideSubgroup q H r → p ≤ r := by
  classical
  obtain ⟨p, hp, hb⟩ := exists_prime_outside_subgroup_le_rationalProfile3000 hq H hH hGRH
  have hex : ∃ r, PrimeOutsideSubgroup q H r := ⟨p, hp⟩
  exact
    ⟨Nat.find hex, Nat.find_spec hex, (Nat.cast_le.mpr (Nat.find_min' hex hp)).trans hb, fun _ hr ↦
      Nat.find_min' hex hr⟩

end PseudoPrime.LLS
