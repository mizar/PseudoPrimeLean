/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.KorseltCanonicalSign

/-! # Proper paired local sign subgroups and reduction

Paired quadratic characters certify properness without an ambient index premise.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Reduction along a divisor preserves membership in a sign subgroup with
the same exponent. Map the positive power and the negative unit value.
This transfers ambient strong-pass units into the paired local modulus. -/
theorem signSubgroup_unitsMap_mem {n m E : ℕ} (hm : m ∣ n) (u : (ZMod n)ˣ)
    (hu : u ∈ signSubgroup n E) : ZMod.unitsMap hm u ∈ signSubgroup m E := by
  change u ^ E = 1 ∨ u ^ E = -1 at hu
  change (ZMod.unitsMap hm u) ^ E = 1 ∨ (ZMod.unitsMap hm u) ^ E = -1
  rcases hu with h | h
  · exact
      Or.inl
        ((map_pow (ZMod.unitsMap hm) u E).symm.trans
          ((congrArg (ZMod.unitsMap hm) h).trans (map_one _)))
  · apply Or.inr
    have hneg : ZMod.unitsMap hm (-1 : (ZMod n)ˣ) = -1 := by
      apply Units.ext
      rw [ZMod.unitsMap_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one, ←
        ZMod.castHom_apply (h := hm), map_neg, map_one]
    exact (map_pow (ZMod.unitsMap hm) u E).symm.trans ((congrArg (ZMod.unitsMap hm) h).trans hneg)

/-- For two distinct odd primes and an exponent that is an odd multiple of
both local half exponents, the sign subgroup modulo their product is proper.
Its paired quadratic annihilator has conductor p*q greater than one.
This supplies the proper local subgroup for the uniform-valuation MR branch. -/
theorem signSubgroup_pair_ne_top_of_local_half_odd {p q E kp kq : ℕ} [Fact p.Prime] [Fact q.Prime]
    [NeZero (p * q)] [Fact (2 < p)] [Fact (2 < q)] (hpOdd : Odd p) (hqOdd : Odd q) (hpq : p ≠ q)
    (hkp : Odd kp) (hkq : Odd kq) (hEp : E = (p / 2) * kp) (hEq : E = (q / 2) * kq) :
    signSubgroup (p * q) E ≠ ⊤ := by
  let χ :=
    (NumberTheory.complexJacobiNumeratorCharacter p hpOdd).changeLevel (dvd_mul_right p q) *
      (NumberTheory.complexJacobiNumeratorCharacter q hqOdd).changeLevel (dvd_mul_left q p)
  have ha : χ ∈ NumberTheory.subgroupAnnihilator (signSubgroup (p * q) E) :=
    paired_quadraticCharacter_mem_signSubgroup_annihilator hpOdd hqOdd (dvd_mul_right p q)
      (dvd_mul_left q p) hkp hkq hEp hEq
  have hc : χ.conductor = p * q :=
    paired_quadraticCharacter_conductor hpOdd hqOdd (dvd_mul_right p q) (dvd_mul_left q p) hpq
  intro ht
  have hχ : χ = 1 :=
    MulChar.eq_one_iff.mpr
      (fun u ↦ (NumberTheory.mem_subgroupAnnihilator_iff _ χ).mp ha u (ht ▸ Subgroup.mem_top u))
  have he := hc.symm.trans (DirichletCharacter.eq_one_iff_conductor_eq_one.mp hχ)
  have hprod : 1 < p * q :=
    (by decide : 1 < 2 * 2).trans_le
      (Nat.mul_le_mul (Fact.out : p.Prime).two_le (Fact.out : q.Prime).two_le)
  exact (Nat.ne_of_gt hprod) he

end PseudoPrime.PrimeTest
